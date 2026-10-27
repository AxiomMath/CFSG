module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab

public section

namespace CFSG.QuasithinUnique.Bridge.Alt57Model

open CFSG.QuasithinUnique.Bridge
open scoped commutatorElement

theorem noAlt57Image_of_mulEquiv {Γ Γ' : Type} [Group Γ] [Group Γ'] (e : Γ' ≃* Γ)
    (h : NoAlt57Image Γ) : NoAlt57Image Γ' := by
  intro H _ π hπ L hL hsq m hm
  exact h H (π.comp e.symm.toMonoidHom) (hπ.comp e.symm.surjective) L hL hsq m hm

theorem card_cases {H : Type} [Group H] {L : Subgroup H} {m : ℕ} (hm : m = 5 ∨ m = 7)
    (e : ↥L ≃* alternatingGroup (Fin m)) : Nat.card L = 60 ∨ Nat.card L = 2520 := by
  rw [Nat.card_congr e.toEquiv]
  rcases hm with rfl | rfl
  · exact Or.inl card_alt_five
  · exact Or.inr card_alt_seven

theorem noAlt57Image_of_simple {Γ : Type} [Group Γ] [IsSimpleGroup Γ] (h60 : Nat.card Γ ≠ 60)
    (h2520 : Nat.card Γ ≠ 2520) : NoAlt57Image Γ := by
  intro H _ π hπ L hL _ m hm ⟨e⟩
  have hc := card_cases hm e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk | hk
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hk
    have hLn : (L.comap π).Normal := hL.comap π
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.comap π) with h | h
    · have hLbot : L = ⊥ := by
        rw [← Subgroup.map_comap_eq_self_of_surjective hπ L, h, Subgroup.map_bot]
      rw [hLbot, Subgroup.card_bot] at hc
      omega
    · have hLtop : L = ⊤ := by
        rw [← Subgroup.map_comap_eq_self_of_surjective hπ L, h, ← MonoidHom.range_eq_map]
        exact MonoidHom.range_eq_top.2 hπ
      have : Nat.card L = Nat.card Γ := by
        rw [hLtop, Subgroup.card_top]
        exact (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ⟩).toEquiv).symm
      omega
  · have hLbot : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      obtain ⟨g, hg⟩ := hπ l
      rw [Subgroup.mem_bot, ← hg]
      exact MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top g)
    rw [hLbot, Subgroup.card_bot] at hc
    omega

theorem noAlt57Image_of_perfect {Γ : Type} [Group Γ] (hperf : Group.IsPerfect Γ)
    (hno : ∀ m : ℕ, (m = 5 ∨ m = 7) → ∀ ψ : Γ →* alternatingGroup (Fin m),
      ¬ Function.Surjective ψ) : NoAlt57Image Γ := by
  intro H _ π hπ L hL hsq m hm ⟨e⟩
  have hHperf : Group.IsPerfect H := Group.IsPerfect.ofSurjective hπ
  have hq2 : ∀ z : H ⧸ L, z * z = 1 := by
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← sq]
    exact hsq z
  have hcomm : ∀ x y : H, ⁅x, y⁆ ∈ L := by
    intro x y
    rw [← QuotientGroup.eq_one_iff]
    have ha := hq2 (QuotientGroup.mk x)
    have hb := hq2 (QuotientGroup.mk y)
    have hab := hq2 (QuotientGroup.mk x * QuotientGroup.mk y)
    have hcm : (QuotientGroup.mk x : H ⧸ L) * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk x := by
      calc (QuotientGroup.mk x : H ⧸ L) * QuotientGroup.mk y
          = QuotientGroup.mk x * ((QuotientGroup.mk x * QuotientGroup.mk y) *
              (QuotientGroup.mk x * QuotientGroup.mk y)) * QuotientGroup.mk y := by
            rw [hab]; simp
        _ = (QuotientGroup.mk x * QuotientGroup.mk x) * QuotientGroup.mk y *
              QuotientGroup.mk x * (QuotientGroup.mk y * QuotientGroup.mk y) := by group
        _ = QuotientGroup.mk y * QuotientGroup.mk x := by rw [ha, hb]; simp
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcm]
    group
  have hLtop : L = ⊤ := by
    rw [eq_top_iff, ← hHperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  let π' : Γ →* ↥L := π.codRestrict L fun g => hLtop ▸ Subgroup.mem_top _
  have hπ' : Function.Surjective π' := by
    intro l
    obtain ⟨g, hg⟩ := hπ l
    exact ⟨g, Subtype.ext hg⟩
  exact hno m hm (e.toMonoidHom.comp π') (e.surjective.comp hπ')

theorem noAlt57Image_of_not_five_dvd {Γ : Type} [Group Γ] [Finite Γ]
    (h : ¬ 5 ∣ Nat.card Γ) : NoAlt57Image Γ := by
  intro H _ π hπ L hL _ m hm ⟨e⟩
  have : Finite H := Finite.of_surjective π hπ
  have h5 : 5 ∣ Nat.card L := by
    rcases card_cases hm e with hc | hc <;> rw [hc] <;> norm_num
  exact h (h5.trans ((Subgroup.card_subgroup_dvd_card L).trans
    (Subgroup.card_dvd_of_surjective hπ)))

open CFSG.ComponentClassification.PresentationLocal in
theorem normal_eq_bot_or_alt_le {M : Subgroup (Equiv.Perm (Fin 6))} (hM : M.Normal) :
    M = ⊥ ∨ alternatingGroup (Fin 6) ≤ M := by
  have hA : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hn : (M.subgroupOf (alternatingGroup (Fin 6))).Normal := hM.subgroupOf _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf (alternatingGroup (Fin 6)))
    with h | h
  · left
    rw [eq_bot_iff]
    intro m hm
    rw [Subgroup.mem_bot]
    have hcent : m ∈ Subgroup.centralizer (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : a * m * a⁻¹ * m⁻¹ ∈ M :=
        M.mul_mem (hM.conj_mem m hm a) (M.inv_mem hm)
      have h2 : a * m * a⁻¹ * m⁻¹ ∈ alternatingGroup (Fin 6) := by
        have := (alternatingGroup.normal (α := Fin 6)).conj_mem a⁻¹ ((alternatingGroup (Fin 6)).inv_mem ha) m
        have h3 := (alternatingGroup (Fin 6)).mul_mem ha this
        simpa [mul_assoc] using h3
      have h3 : (⟨a * m * a⁻¹ * m⁻¹, h2⟩ : alternatingGroup (Fin 6)) ∈
          M.subgroupOf (alternatingGroup (Fin 6)) := h1
      rw [h, Subgroup.mem_bot] at h3
      have h4 : a * m * a⁻¹ * m⁻¹ = 1 := congrArg Subtype.val h3
      calc a * m = (a * m * a⁻¹ * m⁻¹) * (m * a) := by group
        _ = m * a := by rw [h4, one_mul]
    rw [centralizer_alternatingGroup_eq_bot (by simp)] at hcent
    exact hcent
  · right
    intro a ha
    have : (⟨a, ha⟩ : alternatingGroup (Fin 6)) ∈ M.subgroupOf (alternatingGroup (Fin 6)) := by
      rw [h]; trivial
    exact this

theorem noAlt57Image_perm_six : NoAlt57Image (Equiv.Perm (Fin 6)) := by
  intro H _ π hπ L hL _ m hm ⟨e⟩
  have : Finite H := Finite.of_surjective π hπ
  have hc := card_cases hm e
  have hΓ : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := card_alt_six
  have hLH : Nat.card L ∣ Nat.card H := Subgroup.card_subgroup_dvd_card L
  have hker := Subgroup.card_ker_mul_card_of_surjective hπ
  rw [hΓ] at hker
  rcases normal_eq_bot_or_alt_le (π.normal_ker) with hk | hk
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hk
    have hLn : (L.comap π).Normal := hL.comap π
    have hcomap : Nat.card (L.comap π) = Nat.card L := by
      have := Subgroup.card_map_of_injective (K := L.comap π) hinj
      rw [Subgroup.map_comap_eq_self_of_surjective hπ] at this
      exact this.symm
    rcases normal_eq_bot_or_alt_le hLn with h | h
    · rw [h, Subgroup.card_bot] at hcomap
      omega
    · have h1 : 360 ∣ Nat.card (L.comap π) := by
        rw [← hA]; exact Subgroup.card_dvd_of_le h
      have h2 : Nat.card (L.comap π) ∣ 720 := by
        rw [← hΓ]; exact Subgroup.card_subgroup_dvd_card _
      rw [hcomap] at h1 h2
      rcases hc with hc | hc <;> rw [hc] at h1 h2 <;> omega
  · have h1 : 360 ∣ Nat.card π.ker := by
      rw [← hA]; exact Subgroup.card_dvd_of_le hk
    obtain ⟨k, hk'⟩ := h1
    rw [hk'] at hker
    have hpos : 0 < Nat.card H := Nat.card_pos
    have hle : Nat.card H ≤ 2 := by
      by_contra hcon
      push Not at hcon
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0] at hker; omega
      · nlinarith
    have : Nat.card L ≤ 2 := (Nat.le_of_dvd hpos hLH).trans hle
    rcases hc with hc | hc <;> omega

end CFSG.QuasithinUnique.Bridge.Alt57Model

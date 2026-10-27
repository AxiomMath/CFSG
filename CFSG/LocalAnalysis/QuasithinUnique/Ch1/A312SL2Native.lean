module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A129Native
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.A3Structure36BSL2
public import CFSG.Quasithin.Background.DicksonPerfectPSL2

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Quasithin Matrix
open scoped commutatorElement
open CFSG.Quasithin.Dickson (perfect_subgroup_psl2_prime overgroup_alternating_five_psl2_prime
  card_alt_five)

theorem card_sl2_zmod (p : ℕ) [hp : Fact p.Prime] :
    Nat.card (SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  have hq : 1 < p := hp.out.one_lt
  have := Fintype.ofFinite (ZMod p)
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    ZMod.card, show p ^ 2 - p = p * (p - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem commutator_map_eq_self {G H : Type*} [Group G] [Group H] (f : G →* H) {L : Subgroup G}
    (hL : ⁅L, L⁆ = L) : ⁅L.map f, L.map f⁆ = L.map f := by
  rw [← Subgroup.map_commutator, hL]

theorem perfect_subgroup_of_mulEquiv_sl2
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {X : Type}
    [Group X] [Finite X] (e : X ≃* SpecialLinearGroup (Fin 2) (ZMod p)) {L : Subgroup X}
    (hL : ⁅L, L⁆ = L) (hne : L ≠ ⊥) :
    L = ⊤ ∨ Nonempty (↥L ≃* SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  let g : X →* GL (Fin 2) (ZMod p) := SpecialLinearGroup.toGL.comp e.toMonoidHom
  have hg : Function.Injective g := SpecialLinearGroup.toGL_injective.comp e.injective
  have hJperf : Group.IsPerfect ↥(L.map g) :=
    Subgroup.isPerfect_iff.mpr (commutator_map_eq_self g hL)
  have hJne : L.map g ≠ ⊥ := (Subgroup.map_eq_bot_iff_of_injective L hg).not.mpr hne
  rcases CFSG.RankThree.SubgroupLists.perfect_gl2_mulEquiv hp2 (L.map g) hJne with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · left
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr (Subgroup.equivMapOfInjective L g hg).toEquiv, Nat.card_congr f.toEquiv,
      Nat.card_congr e.toEquiv]
  · right
    exact ⟨(Subgroup.equivMapOfInjective L g hg).trans f⟩

theorem sixteen_dvd_of_mod_eight {p : ℕ} (h : p % 8 = 1 ∨ p % 8 = 7) :
    16 ∣ p * (p ^ 2 - 1) := by
  have h16 : p % 16 = 1 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 15 := by omega
  have hsq : p ^ 2 % 16 = 1 := by
    rcases h16 with h | h | h | h <;> simp [Nat.pow_mod, h]
  have hle : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  exact Dvd.dvd.mul_left (by omega) p

theorem a312SL2Fact : A312SL2Fact := by
  intro p hp hp3 X _ _ hX S hS B hB hBtop
  obtain ⟨e⟩ := hX
  have hpf : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hB' : B ∈ cComp (B ⊔ S) := hB
  have hBperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB'
  have hBne : B ≠ ⊥ := ne_bot_of_mem_cComp hB'
  rcases perfect_subgroup_of_mulEquiv_sl2 hp2 e hBperf hBne with hBt | ⟨⟨e5⟩⟩
  · exact absurd hBt hBtop
  have hB120 : Nat.card B = 120 := (Nat.card_congr e5.toEquiv).trans card_sl2_five
  have hX : Nat.card X = p * (p ^ 2 - 1) := (Nat.card_congr e.toEquiv).trans (card_sl2_zmod p)
  have hp5ne : p ≠ 5 := by
    rintro rfl
    apply hBtop
    apply Subgroup.eq_top_of_card_eq
    rw [hB120, hX]
    norm_num
  have hmod5 : p ^ 2 % 5 = 1 := by
    have hd := Subgroup.card_subgroup_dvd_card B
    rw [hB120, hX] at hd
    have h5 : 5 ∣ p * (p ^ 2 - 1) := (by norm_num : 5 ∣ 120).trans hd
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h).symm hp5ne
    · have hle : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
      generalize p ^ 2 = n at h hle ⊢
      omega
  have hXq : CFSG.IsQuasisimple X :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (A36B.isQuasisimple_sl2 hp hp5)
  let ρ : X →* ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)))).comp e.toMonoidHom
  have hρ : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hKc : ∀ k ∈ ρ.ker, k ∈ Subgroup.center X := by
    intro k hk
    have hk1 : QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)))
        (e k) = 1 := hk
    have hek : e k ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) :=
      (QuotientGroup.eq_one_iff _).mp hk1
    rw [Subgroup.mem_center_iff] at hek ⊢
    intro x
    exact e.injective (by simpa using hek (e x))
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hlift : ∀ L : Subgroup X, L.map ρ = ⊤ → L = ⊤ := by
    intro L hL
    have hXperf : ⁅(⊤ : Subgroup X), ⊤⁆ = ⊤ := Group.isPerfect_def.mp hXq.1
    rw [eq_top_iff, ← hXperf, Subgroup.commutator_le]
    intro a _ b _
    have hmem : ∀ x : X, ∃ y ∈ L, y⁻¹ * x ∈ ρ.ker := by
      intro x
      have : ρ x ∈ L.map ρ := hL ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := this
      refine ⟨y, hy, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    obtain ⟨y₁, hy₁, hk₁⟩ := hmem a
    obtain ⟨y₂, hy₂, hk₂⟩ := hmem b
    have e1 : a = y₁ * (y₁⁻¹ * a) := by group
    have e2 : b = y₂ * (y₂⁻¹ * b) := by group
    have hc : ⁅a, b⁆ = ⁅y₁, y₂⁆ := by
      calc ⁅a, b⁆ = ⁅y₁ * (y₁⁻¹ * a), y₂ * (y₂⁻¹ * b)⁆ := by rw [← e1, ← e2]
        _ = ⁅y₁, y₂ * (y₂⁻¹ * b)⁆ := commutatorElement_mul_center_left _ (hKc _ hk₁)
        _ = ⁅y₁, y₂⁆ := commutatorElement_mul_center_right _ (hKc _ hk₂)
    rw [hc, commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hy₁ hy₂) (L.inv_mem hy₁)) (L.inv_mem hy₂)
  set Y : Subgroup X := B ⊔ S with hYdef
  have hBY : B ≤ Y := le_sup_left
  have hSY : S ≤ Y := le_sup_right
  have hBbperf : ⁅B.map ρ, B.map ρ⁆ = B.map ρ := commutator_map_eq_self ρ hBperf
  have hnotcentral : ¬ B ≤ Subgroup.center X := by
    intro hcen
    apply hBne
    calc B = ⁅B, B⁆ := hBperf.symm
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (hcen.trans (Subgroup.center_le_centralizer _))
  have hBbne : B.map ρ ≠ ⊥ := by
    intro h
    exact hnotcentral fun x hx => hKc x (((Subgroup.map_eq_bot_iff B).mp h) hx)
  rcases perfect_subgroup_psl2_prime hp2 (B.map ρ) hBbperf hBbne with hBbtop | ⟨⟨e5'⟩, -⟩
  · exact absurd (hlift B hBbtop) hBtop
  have hBb60 : Nat.card (B.map ρ) = 60 := (Nat.card_congr e5'.toEquiv).trans card_alt_five
  have hSB : S ≤ B := by
    rcases overgroup_alternating_five_psl2_prime hp2 (Subgroup.map_mono hBY) ⟨e5'⟩ with
      hYtop | hY60
    · exfalso
      have hYt : Y = ⊤ := hlift Y hYtop
      have hsub : CFSG.Open.IsSubnormal B ⊤ := by
        have := subnormal_of_mem_cComp hB'
        rwa [hYt] at this
      rcases A3.eq_top_or_le_center_of_subnormal hXq (A3.subnormal_top_iff.mp hsub) with h | h
      · exact hBtop h
      · exact hnotcentral h
    · have hYb : Y.map ρ = B.map ρ :=
        (Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hBY) (hY60.trans hBb60.symm).le).symm
      have hpre : (B.map ρ).comap ρ = B := by
        symm
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.le_comap_map ρ B)
        have hind : ((B.map ρ).comap ρ).index = (B.map ρ).index :=
          Subgroup.index_comap_of_surjective (B.map ρ) hρ
        have hc1 := Subgroup.card_mul_index ((B.map ρ).comap ρ)
        have hc2 := Subgroup.card_mul_index (B.map ρ)
        have h3 : Nat.card X = Nat.card (ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) * 2 := by
          rw [Nat.card_congr e.toEquiv]
          exact CFSG.RankThree.SubgroupLists.natCard_sl2_eq h2
        have hi : 0 < (B.map ρ).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        rw [hind] at hc1
        have hmul : Nat.card ((B.map ρ).comap ρ) * (B.map ρ).index =
            120 * (B.map ρ).index := by
          rw [hc1, h3, ← hc2, hBb60]
          ring
        rw [hB120]
        exact (Nat.eq_of_mul_eq_mul_right hi hmul).le
      calc S ≤ Y := hSY
        _ ≤ (Y.map ρ).comap ρ := Subgroup.le_comap_map ρ Y
        _ = B := by rw [hYb, hpre]
  have hmod8 : p % 8 = 3 ∨ p % 8 = 5 := by
    have hSdvd : Nat.card S ∣ 120 := hB120 ▸ Subgroup.card_dvd_of_le hSB
    obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
    have hidx : ¬ 2 ∣ S.index := by
      have := hS.2.2
      change ¬ 2 ∣ S.relIndex ⊤ at this
      rwa [Subgroup.relIndex_top_right] at this
    have hXS : Nat.card X = Nat.card S * S.index := (Subgroup.card_mul_index S).symm
    have hpodd : p % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hp with h | h
      · exact absurd h hp2
      · exact h
    by_contra hcon
    have h18 : p % 8 = 1 ∨ p % 8 = 7 := by omega
    have h16 := sixteen_dvd_of_mod_eight h18
    rw [← hX, hXS, hk] at h16
    have hcop : Nat.Coprime (2 ^ 4) S.index :=
      Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
    have h16' : 2 ^ 4 ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right h16
    have h120 : 2 ^ 4 ∣ 120 := h16'.trans (hk ▸ hSdvd)
    norm_num at h120
  exact ⟨⟨e5⟩, hmod5, hmod8⟩

end CFSG.QuasithinUnique.Vol2Native

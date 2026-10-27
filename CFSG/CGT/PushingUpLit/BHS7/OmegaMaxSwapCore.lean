module

public import CFSG.CGT.PushingUpLit.BHS6.BlockStructure
public import CFSG.CGT.PushingUpLit.BHS7.OmegaMaxSwapPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

namespace OMS

variable {Γ : Type} [Group Γ]

theorem card_conjSub_eq (g : Γ) (H : Subgroup Γ) : Nat.card (A1b.conjSub g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isElemAbelian_conjSub {A : Subgroup Γ} (hA : IsElemAbelian 2 A) (g : Γ) :
    IsElemAbelian 2 (A1b.conjSub g A) := by
  rw [B6.isElemAbelian_iff] at hA ⊢
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [A1b.mem_conjSub_iff] at ha hb
    have := hA.1 _ ha _ hb
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = b * a := by group
  · rw [A1b.mem_conjSub_iff] at ha
    have h2 := hA.2 _ ha
    have h1 : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    calc a ^ 2 = (g * (g⁻¹ * a * g) * g⁻¹) ^ 2 := by rw [← h1]
      _ = g * (g⁻¹ * a * g) ^ 2 * g⁻¹ := conj_pow
      _ = 1 := by rw [h2]; group

theorem isMaxElemAbelian_conjSub_of_le {T A : Subgroup Γ} (hA : IsMaxElemAbelian T A) (g : Γ)
    (hg : A1b.conjSub g A ≤ T) : IsMaxElemAbelian T (A1b.conjSub g A) :=
  ⟨hg, isElemAbelian_conjSub hA.2.1 g, fun B hB hBe =>
    (hA.2.2 B hB hBe).trans_eq (card_conjSub_eq g A).symm⟩

theorem conjSub_thompsonJ_le {T : Subgroup Γ} {g : Γ} (h : A1b.conjSub g (thompsonJ T) ≤ T) :
    A1b.conjSub g (thompsonJ T) ≤ thompsonJ T := by
  unfold A1b.conjSub thompsonJ at h ⊢
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun A hA => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hAJ : A ≤ ⨆ (A : Subgroup Γ) (_ : IsMaxElemAbelian T A), A := le_iSup₂_of_le A hA le_rfl
  have hAgT : A1b.conjSub g A ≤ T := (Subgroup.map_mono hAJ).trans h
  exact le_iSup₂_of_le (A1b.conjSub g A) (isMaxElemAbelian_conjSub_of_le hA g hAgT) le_rfl

section Finite

variable [Finite Γ]

theorem eq_of_isSylowTwoOf_le {S H R : Subgroup Γ} (hS : IsSylowTwoOf S H) (hRH : R ≤ H)
    (hR : IsPGroup 2 ↥R) (hSR : S ≤ R) : S = R := by
  obtain ⟨R', hR', hRR'⟩ := B6.exists_isSylowTwoOf_ge hR hRH
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hS hR'
  have hcard : Nat.card R' = Nat.card S := by rw [hg]; exact card_conjSub_eq g S
  have h1 : S = R' := Subgroup.eq_of_le_of_card_ge (hSR.trans hRR') hcard.le
  exact le_antisymm hSR (h1 ▸ hRR')

theorem isSylowTwoOf_inf_sup {T E B : Subgroup Γ} (hT : IsPGroup 2 ↥T) (hBT : B ≤ T)
    (hBE : B ≤ Subgroup.normalizer (E : Set Γ)) (hS : IsSylowTwoOf (T ⊓ E) E) :
    IsSylowTwoOf (T ⊓ (E ⊔ B)) (E ⊔ B) := by
  have hT2 : IsPGroup 2 ↥(T ⊓ (E ⊔ B)) := hT.to_le inf_le_left
  obtain ⟨T', hT', hTT'⟩ := B6.exists_isSylowTwoOf_ge hT2 (inf_le_right : T ⊓ (E ⊔ B) ≤ E ⊔ B)
  have hBT' : B ≤ T' := (le_inf hBT le_sup_right).trans hTT'
  have hle : T' ≤ T ⊓ (E ⊔ B) := by
    intro t ht
    have htH : t ∈ B ⊔ E := by rw [sup_comm]; exact hT'.1 ht
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right B E hBE] at htH
    obtain ⟨b, hb, e, he, rfl⟩ := htH
    have heT' : e ∈ T' := by
      have := T'.mul_mem (T'.inv_mem (hBT' hb)) ht
      simpa using this
    have hSiT' : T ⊓ E ≤ T' ⊓ E :=
      le_inf ((inf_le_inf_left T le_sup_left).trans hTT') inf_le_right
    have hR2 : IsPGroup 2 ↥(T' ⊓ E) := hT'.2.1.to_le inf_le_left
    have hEq : T ⊓ E = T' ⊓ E := eq_of_isSylowTwoOf_le hS inf_le_right hR2 hSiT'
    have heT : e ∈ T := by
      have : e ∈ T' ⊓ E := ⟨heT', he⟩
      rw [← hEq] at this
      exact this.1
    exact ⟨T.mul_mem (hBT hb) heT,
      (E ⊔ B).mul_mem (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left he)⟩
  rw [le_antisymm hTT' hle]
  exact hT'

theorem inf_centralizer_le_of_isSylowTwoOf {S E B : Subgroup Γ}
    (hBE : B ≤ Subgroup.normalizer (E : Set Γ))
    (h2 : ∀ c ∈ E ⊔ B, c ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) → ∃ k : ℕ, c ^ 2 ^ k = 1)
    (hS : IsSylowTwoOf S (E ⊔ B)) :
    (E ⊔ B) ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) ≤ S := by
  set H : Subgroup Γ := E ⊔ B
  set W : Subgroup Γ := pCoreOf 2 E
  set C : Subgroup Γ := H ⊓ Subgroup.centralizer (W : Set Γ)
  have hHW : H ≤ Subgroup.normalizer (W : Set Γ) :=
    sup_le (le_normalizer_pCoreOf_self E)
      (hBE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E))
  have hC2 : IsPGroup 2 ↥C := fun c => by
    obtain ⟨k, hk⟩ := h2 c c.2.1 c.2.2
    exact ⟨k, Subtype.ext hk⟩
  have key : ∀ z ∈ H, ∀ c ∈ C, z * c * z⁻¹ ∈ C := by
    intro z hz c hc
    refine ⟨H.mul_mem (H.mul_mem hz hc.1) (H.inv_mem hz),
      Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hw' : z⁻¹ * w * z ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hHW (H.inv_mem hz)) w).mp hw
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ hw'
    calc w * (z * c * z⁻¹) = z * ((z⁻¹ * w * z) * c) * z⁻¹ := by group
      _ = z * (c * (z⁻¹ * w * z)) * z⁻¹ := by rw [hcomm]
      _ = (z * c * z⁻¹) * w := by group
  have hHC : H ≤ Subgroup.normalizer (C : Set Γ) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
    have := key g⁻¹ (H.inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hHC hC2).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hS)

end Finite

end OMS

section Main

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

theorem card_autOn_baum_of_isSylowTwoOf (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) {m : ℕ} (hm2 : 2 ≤ m) (hn : IsNaturalAltModule ↥E m)
    (hS : IsSylowTwoOf (T ⊓ E) E)
    (hC : ∀ c ∈ E ⊔ baum T, c ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) →
      ∃ k : ℕ, c ^ 2 ^ k = 1) :
    Nat.card ↥(autOn (baum T) (pCoreOf 2 E)) = 2 ^ m := by
  classical
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  obtain ⟨_, ψ, -, -, hψbij, hsup, hJeq, k, hk1, -, hswap, hcard, -⟩ :=
    block_structure_alt hG hT hE hm2 hn hWdef hWe
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  set H : Subgroup Γ := E ⊔ baum T
  have hHW : H ≤ Subgroup.normalizer (W : Set Γ) := sup_le hEW hBW
  have hHE : H ≤ Subgroup.normalizer (E : Set Γ) := sup_le Subgroup.le_normalizer hBE
  have hBT : baum T ≤ T := inf_le_left
  have hJB : thompsonJ T ≤ baum T := B6.thompsonJ_le_baum T
  have hBH : baum T ≤ H := le_sup_right
  have hJH : thompsonJ T ≤ H := hJB.trans hBH
  have hSH : IsSylowTwoOf (T ⊓ H) H := OMS.isSylowTwoOf_inf_sup hT2.2.1 hBT hBE hS
  have hker : H ⊓ Subgroup.centralizer (W : Set Γ) ≤ T ⊓ H :=
    OMS.inf_centralizer_le_of_isSylowTwoOf hBE hC hSH
  let N : Subgroup (MulAut ↥W) := Subgroup.normalizer (autOn E W : Set (MulAut ↥W))
  have hautH : autOn H W ≤ N := autOn_le_normalizer_autOn hHW hHE
  let act : ↥H →* ↥N := (actOn W H hHW).codRestrict N (fun x =>
    hautH (by rw [← range_actOn W H hHW]; exact ⟨x, rfl⟩))
  have hact : ∀ x, ((act x : ↥N) : MulAut ↥W) = actOn W H hHW x := fun x => rfl
  have hrange : ∀ y : ↥N, ∃ x : ↥H, act x = y := fun y => by
    have h1 : (y : MulAut ↥W) ∈ autOn H W := by
      have : (y : MulAut ↥W) ∈ autOn E W ⊔ autOn (baum T) W := by rw [hsup]; exact y.2
      exact sup_le (autOn_le_autOn W le_sup_left) (autOn_le_autOn W le_sup_right) this
    rw [← range_actOn W H hHW] at h1
    obtain ⟨x, hx⟩ := h1
    exact ⟨x, Subtype.ext hx⟩
  let Φ : ↥H →* Equiv.Perm (Fin (2 * m + 1)) := ψ.comp act
  have hsurj : Function.Surjective Φ := fun p => by
    obtain ⟨y, rfl⟩ := hψbij.2 p
    obtain ⟨x, hx⟩ := hrange y
    exact ⟨x, by simp [Φ, hx]⟩
  have hΦker : ∀ x : ↥H, Φ x = 1 → (x : Γ) ∈ T := by
    intro x hx
    have h1 : act x = 1 := by
      apply hψbij.1
      rw [map_one]
      exact hx
    have h2 : x ∈ (actOn W H hHW).ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
    rw [ker_actOn, Subgroup.mem_subgroupOf] at h2
    exact (hker h2).1
  let Bbar : Subgroup (Equiv.Perm (Fin (2 * m + 1))) := ((autOn (baum T) W).subgroupOf N).map ψ
  have hF1 : ∀ (b : Γ) (hb : b ∈ baum T), Φ ⟨b, hBH hb⟩ ∈ Bbar := by
    intro b hb
    refine Subgroup.mem_map.mpr ⟨act ⟨b, hBH hb⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, hact]
    exact mem_autOn_iff.mpr ⟨⟨b, hBW hb⟩, hb, rfl⟩
  have hF2 : ∀ y ∈ Bbar, ∃ (j : Γ) (hj : j ∈ thompsonJ T), Φ ⟨j, hJH hj⟩ = y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hz' : (z : MulAut ↥W) ∈ autOn (thompsonJ T) W := by
      rw [hJeq]
      exact Subgroup.mem_subgroupOf.mp hz
    obtain ⟨a, haJ, haz⟩ := mem_autOn_iff.mp hz'
    refine ⟨a, haJ, ?_⟩
    show ψ (act ⟨(a : Γ), hJH haJ⟩) = ψ z
    congr 1
    apply Subtype.ext
    rw [hact]
    exact haz
  let P : Subgroup (Equiv.Perm (Fin (2 * m + 1))) := ((T ⊓ H).subgroupOf H).map Φ
  have hS0 : IsPGroup 2 ↥((T ⊓ H).subgroupOf H) :=
    hSH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH.1).symm
  have hP2 : IsPGroup 2 ↥P := hS0.map Φ
  have hPidx : ¬ 2 ∣ P.index := fun hd => hSH.2.2 (hd.trans (Subgroup.index_map_dvd _ hsurj))
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have hY : ∃ Y ≤ P, IsMaxSwapGroup Y := exists_isMaxSwapGroup_le_of_isSylow hodd hP2 hPidx
  have hstar : ∀ π : Equiv.Perm (Fin (2 * m + 1)),
      A1b.conjSub π Bbar ≤ P → A1b.conjSub π Bbar = Bbar := by
    intro π hπ
    obtain ⟨g, rfl⟩ := hsurj π
    have hΦconj : ∀ (x j : Γ) (hx : x ∈ H) (hj : j ∈ H), x = (g : Γ) * j * (g : Γ)⁻¹ →
        Φ ⟨x, hx⟩ = Φ g * Φ ⟨j, hj⟩ * (Φ g)⁻¹ := by
      intro x j hx hj hxj
      have : (⟨x, hx⟩ : ↥H) = g * ⟨j, hj⟩ * g⁻¹ := Subtype.ext hxj
      rw [this, map_mul, map_mul, map_inv]
    have h1 : A1b.conjSub (g : Γ) (thompsonJ T) ≤ T := by
      intro x hx
      rw [A1b.mem_conjSub_iff] at hx
      have hjJ : (g : Γ)⁻¹ * x * g ∈ thompsonJ T := hx
      have hxj : x = (g : Γ) * ((g : Γ)⁻¹ * x * g) * (g : Γ)⁻¹ := by group
      have hxH : x ∈ H := by
        have h' : (g : Γ) * ((g : Γ)⁻¹ * x * g) * (g : Γ)⁻¹ ∈ H :=
          H.mul_mem (H.mul_mem g.2 (hJH hjJ)) (H.inv_mem g.2)
        rwa [← hxj] at h'
      have hmem : Φ ⟨x, hxH⟩ ∈ P := by
        rw [hΦconj x _ hxH (hJH hjJ) hxj]
        exact hπ (A1b.mem_conjSub_of_mem (hF1 _ (hJB hjJ)))
      obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hmem
      have hker1 : Φ (⟨x, hxH⟩ * s⁻¹) = 1 := by
        rw [map_mul, map_inv, hsx, mul_inv_cancel]
      have hxs : (x : Γ) * (s : Γ)⁻¹ ∈ T := hΦker _ hker1
      have hsT : (s : Γ) ∈ T := (Subgroup.mem_subgroupOf.mp hs).1
      simpa using T.mul_mem hxs hsT
    have h2 : A1b.conjSub (g : Γ) (thompsonJ T) ≤ thompsonJ T := OMS.conjSub_thompsonJ_le h1
    have h3 : A1b.conjSub (Φ g) Bbar ≤ Bbar := by
      intro y hy
      rw [A1b.mem_conjSub_iff] at hy
      obtain ⟨j, hjJ, hj⟩ := hF2 _ hy
      have hgj : (g : Γ) * j * (g : Γ)⁻¹ ∈ thompsonJ T := h2 (A1b.mem_conjSub_of_mem hjJ)
      have hy' : y = Φ ⟨(g : Γ) * j * (g : Γ)⁻¹, hJH hgj⟩ := by
        rw [hΦconj _ j (hJH hgj) (hJH hjJ) rfl, hj]
        group
      rw [hy']
      exact hF1 _ (hJB hgj)
    exact Subgroup.eq_of_le_of_card_ge h3 (OMS.card_conjSub_eq (Φ g) Bbar).ge
  have hk : k = (2 * m + 1 - 1) / 2 := swap_rank_eq_of_unique_conj hodd hswap hk1 hY hstar
  have hkm : k = m := by omega
  rw [hcard, hkm]

end Main

end CFSG.CGT.PushingUpLit.BHS7

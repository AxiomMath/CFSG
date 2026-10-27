module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCoverBasic

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

section Grp

variable {H : Type} [Group H]

theorem commutatorElement_mul_central_left {x y z : H} (hz : z ∈ center H) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hzy : z * y = y * z := (mem_center_iff.mp hz y).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * z * y * (z⁻¹ * x⁻¹) * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hzy]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_central_right {x y z : H} (hz : z ∈ center H) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have hzx : z * x⁻¹ = x⁻¹ * z := (mem_center_iff.mp hz x⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * (y * z) * x⁻¹ * (z⁻¹ * y⁻¹) = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzx]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem le_of_map_le_of_perfect {H₁ : Type*} [Group H₁] (f : H →* H₁) (hf : f.ker ≤ center H)
    {K L : Subgroup H} (hK : ⁅K, K⁆ = K) (hKL : K.map f ≤ L.map f) : K ≤ L := by
  have h1 : K ≤ L ⊔ f.ker := by
    rw [← Subgroup.comap_map_eq]
    exact map_le_iff_le_comap.mp hKL
  have hker : f.ker ≤ normalizer (L : Set H) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro l
    rw [← mem_center_iff.mp (hf hn) l, mul_inv_cancel_right]
  calc K = ⁅K, K⁆ := hK.symm
    _ ≤ ⁅L ⊔ f.ker, L ⊔ f.ker⁆ := commutator_mono h1 h1
    _ ≤ L := by
      rw [commutator_le]
      intro a ha b hb
      obtain ⟨l₁, hl₁, n₁, hn₁, rfl⟩ := Sol76.exists_mul_of_mem_sup_normalizer hker ha
      obtain ⟨l₂, hl₂, n₂, hn₂, rfl⟩ := Sol76.exists_mul_of_mem_sup_normalizer hker hb
      rw [commutatorElement_mul_central_left (hf hn₁), commutatorElement_mul_central_right (hf hn₂),
        commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hl₁ hl₂) (inv_mem hl₁)) (inv_mem hl₂)

variable [Finite H]

theorem gsFixedLayer_eq_self {L Y : Subgroup H} {y : H} (hLY : L ≤ Y)
    (hL : IsPComponent 2 (L.subgroupOf Y)) (hLy : L ≤ centralizer ({y} : Set H)) :
    UnbalancedGS.gsFixedLayer L y = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ K : Subgroup H, K = L → (pLayer ↥K 2).map K.subtype = L := by
    rintro K rfl
    obtain ⟨-, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K Y hLY).mp hL
    have hKK : IsPComponent 2 (K.subgroupOf K) :=
      (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K K le_rfl).mpr
        ⟨by rw [subgroupOf_self]; exact IsSubnormal.top, hres, hq⟩
    rw [subgroupOf_self] at hKK
    have htop : pLayer ↥K 2 = ⊤ := eq_top_iff.mpr (le_sSup hKK)
    rw [htop, ← MonoidHom.range_eq_map, range_subtype]
  exact key _ (inf_eq_left.mpr hLy)

theorem exists_card_lt_of_swap
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) {x y : H} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hyZ : y ∈ center H) {L M Q : Subgroup H} {m : ℕ}
    (hLx : L ≤ centralizer ({x} : Set H))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set H)))) (hyL : y ∈ L)
    (hm : Odd m) (hm7 : 7 ≤ m)
    (eL : Nonempty (↥L ⧸ Open.fusionZStar ↥L ≃* alternatingGroup (Fin m)))
    (hM : IsPComponent 2 M) (hMx : conjugate M x ≠ M) (hLM : L ≤ M ⊔ conjugate M x)
    (hLMpc : IsPComponent 2 (L.subgroupOf ((M ⊔ conjugate M x) ⊓ centralizer ({x} : Set H))))
    (hQ : IsPGroup 2 Q) (hQx : Q ≤ centralizer ({x} : Set H))
    (hQL : Q ≤ coreActionKernel L) :
    ∃ P : Subgroup H, IsPGroup 2 P ∧ P ≤ coreActionKernel M ∧ Nat.card Q < Nat.card P := by
  have hCy : centralizer ({y} : Set H) = ⊤ := by
    refine eq_top_iff.mpr fun w _ => ?_
    rw [mem_centralizer_singleton_iff]
    exact mem_center_iff.mp hyZ w
  have hLy : L ≤ centralizer ({y} : Set H) := by rw [hCy]; exact le_top
  have hGL : UnbalancedGS.gsFixedLayer L y = L := gsFixedLayer_eq_self hLx hL hLy
  have hP : Sol78.IsDoublePair x L m :=
    ⟨hx, hLx, hL, hm, hm7, Sol78.fusionZStar_ne_of_central_involution hy hyL hLy, eL⟩
  have hcore : ∀ K : Subgroup H, K = L →
      (pPrimeCore 2 ↥K).map K.subtype = K ⊓ (pPrimeCore 2 ↥L).map L.subtype := by
    rintro K rfl
    exact (inf_eq_right.mpr (map_subtype_le _)).symm
  obtain ⟨-, P, hP2, hPK, hlt⟩ := Sol78.swap_pump_up hSchur hP hy
    (by rw [hGL]; exact le_inf hLx hLy) (hcore _ hGL)
    (Sol78.coreQuotCongr (MulEquiv.subgroupCongr hGL)) (by rw [hGL]; exact hyL)
    (by rw [hCy]; exact le_top) (by rw [hCy]; exact (isPComponent_subgroupOf_top_iff _).mpr hM)
    (by rw [hGL]; exact hLM) (by rw [hGL]; exact hLMpc) hMx hQ hQx hQL
    (by rw [hCy]; exact le_top)
  exact ⟨P, hP2, hPK.trans inf_le_right, hlt⟩

theorem card_lt_card_inf_comap {Y N : Subgroup H} [N.Normal] (hYn : Y.Normal) {x : H}
    (hsup : Y ⊔ zpowers x = ⊤) {Q : Subgroup H} (hQY : Q ≤ Y) {P' : Subgroup (H ⧸ N)}
    (hlt : Nat.card ↥(Q.map (QuotientGroup.mk' N) ⊔ zpowers (QuotientGroup.mk' N x)) <
      Nat.card P') :
    Nat.card Q < Nat.card ↥(Y ⊓ P'.comap (QuotientGroup.mk' N)) := by
  classical
  set f := QuotientGroup.mk' N with hf
  set Y₁ := Y.map f with hY₁
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective N
  have : Y₁.Normal := hYn.map f hfs
  have hsup₁ : zpowers (f x) ⊔ Y₁ = ⊤ := by
    rw [sup_comm, hY₁, ← MonoidHom.map_zpowers, ← Subgroup.map_sup, hsup,
      Subgroup.map_top_of_surjective f hfs]
  set Q' := Q.map f ⊔ zpowers (f x) with hQ'
  have hidx : Y₁.index = Y₁.relIndex (zpowers (f x)) := by
    have h := relIndex_sup_right (zpowers (f x)) Y₁
    rwa [hsup₁, relIndex_top_right] at h
  have hidx' : Y₁.index ≤ Y₁.relIndex Q' := by
    rw [hidx]
    exact relIndex_le_of_le_right le_sup_right
      (Subgroup.index_ne_zero_of_finite (H := Y₁.subgroupOf Q'))
  have hidx0 : 0 < Y₁.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Y₁))
  have hQ'card : Y₁.index * Nat.card ↥(Q.map f) ≤ Nat.card Q' := by
    rw [← relIndex_mul_card (H := Y₁) (K := Q')]
    exact Nat.mul_le_mul hidx' (Subgroup.card_le_of_le (le_inf (map_mono hQY) le_sup_left))
  have hP'card : Nat.card P' ≤ Y₁.index * Nat.card ↥(Y₁ ⊓ P') := by
    rw [← relIndex_mul_card (H := Y₁) (K := P')]
    exact Nat.mul_le_mul_right _ (Nat.le_of_dvd hidx0 (relIndex_dvd_index_of_normal Y₁ P'))
  have hmain : Nat.card ↥(Q.map f) < Nat.card ↥(Y₁ ⊓ P') :=
    Nat.lt_of_mul_lt_mul_left (a := Y₁.index) (by omega)
  have hfk : f.ker = N := QuotientGroup.ker_mk' N
  have hcardS : ∀ S : Subgroup H, Nat.card S = Nat.card ↥(S.map f) * Nat.card ↥(N ⊓ S) := by
    intro S
    rw [← relIndex_mul_card (H := f.ker) (K := S), relIndex_ker, hfk]
  set S := Y ⊓ P'.comap f with hS
  have hSmap : S.map f = Y₁ ⊓ P' := GSThmB.TwoQuot.map_inf_comap f Y P'
  have hNS : N ⊓ Q ≤ N ⊓ S := by
    refine le_inf inf_le_left (le_inf (inf_le_right.trans hQY) ?_)
    intro n hn
    rw [mem_comap, hf, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr
      (mem_inf.mp hn).1]
    exact one_mem _
  have h1 := Subgroup.card_le_of_le hNS
  have h2 : 0 < Nat.card ↥(N ⊓ S) := Nat.card_pos
  rw [hcardS Q, hcardS S, hSmap]
  calc Nat.card ↥(Q.map f) * Nat.card ↥(N ⊓ Q) ≤ Nat.card ↥(Q.map f) * Nat.card ↥(N ⊓ S) :=
        Nat.mul_le_mul_left _ h1
    _ < Nat.card ↥(Y₁ ⊓ P') * Nat.card ↥(N ⊓ S) := Nat.mul_lt_mul_of_pos_right hmain h2

end Grp

theorem mem_coreActionKernel_of_forall_commute {H : Type*} [Group H] {L : Subgroup H} {g : H}
    (hg : ∀ l ∈ L, l * g = g * l) : g ∈ coreActionKernel L := by
  refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      rw [← hg l hl, mul_inv_cancel_right]
      exact hl
    · intro hl
      have h1 := hg _ hl
      have e : l = g * l * g⁻¹ := by
        calc l = g⁻¹ * (g * l * g⁻¹ * g) := by group
          _ = g⁻¹ * (g * (g * l * g⁻¹)) := by rw [h1]
          _ = g * l * g⁻¹ := by group
      rw [e]
      exact hl
  · rw [show j⁻¹ * g⁻¹ * j * g = 1 by
      calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
        _ = j⁻¹ * g⁻¹ * (g * j) := by rw [hg j hj]
        _ = 1 := by group]
    exact one_mem _

theorem fusionZStar_le_sup_zpowers_map {P P₁ : Type*} [Group P] [Finite P] [Group P₁]
    [Finite P₁] (φ : P →* P₁) (hφs : Function.Surjective φ) (hφc : φ.ker ≤ center P)
    (hq : IsQuasisimple (P ⧸ pPrimeCore 2 P))
    (hZ : Nat.card (center (P ⧸ pPrimeCore 2 P)) ≤ 2) {y : P} (hy : orderOf y = 2)
    (hyc : QuotientGroup.mk' (pPrimeCore 2 P) y ∈ center (P ⧸ pPrimeCore 2 P)) :
    Open.fusionZStar P₁ ≤ pPrimeCore 2 P₁ ⊔ zpowers (φ y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z₁ hz₁
  obtain ⟨z, rfl⟩ := hφs z₁
  have hz : z ∈ Open.fusionZStar P := by
    rw [← GSThmB.TwoQuot.comap_fusionZStar_of_central φ hφs hφc hq]
    exact hz₁
  have h2 : φ z ∈ (pPrimeCore 2 P ⊔ zpowers y).map φ :=
    mem_map_of_mem φ (fusionZStar_le_sup_zpowers hy hyc hZ hz)
  rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h2
  exact sup_le_sup_right (CatalogueBCentralQuotient.primeCore_map_le 2 φ hφs) _ h2

end CFSG.ComponentClassification.SolMax

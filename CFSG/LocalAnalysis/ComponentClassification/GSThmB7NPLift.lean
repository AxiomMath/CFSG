module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7TransL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Prod
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups Pointwise commutatorElement

namespace Seven

section Odd

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mk_mem {N : Subgroup G} {t : G} (hNt : N ≤ centralizer ({t} : Set G))
    (ht : t * t = 1)
    (hmem : QuotientGroup.mk' (pPrimeCore 2 G) t ∈ N.map (QuotientGroup.mk' (pPrimeCore 2 G))) :
    t ∈ N := by
  obtain ⟨n, hn, hnt⟩ := mem_map.mp hmem
  have hu : n⁻¹ * t ∈ pPrimeCore 2 G := by
    rw [← QuotientGroup.eq]
    exact hnt
  have hnt' : n * t = t * n := mem_centralizer_singleton_iff.mp (hNt hn)
  have hcomm : Commute n (n⁻¹ * t) := by
    show n * (n⁻¹ * t) = n⁻¹ * t * n
    calc n * (n⁻¹ * t) = n⁻¹ * (n * t) := by group
      _ = n⁻¹ * (t * n) := by rw [hnt']
      _ = n⁻¹ * t * n := by group
  have hodd : Odd (orderOf (n⁻¹ * t)) := by
    have h1 : orderOf (n⁻¹ * t) ∣ Nat.card (pPrimeCore 2 G) :=
      Subgroup.orderOf_dvd_natCard _ hu
    have h2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 G) := fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h3 => h2 (h3.trans h1))
  obtain ⟨k, hk⟩ := hodd
  have htk : t ^ (orderOf (n⁻¹ * t)) = t := by
    rw [hk, pow_succ, pow_mul, sq, ht, one_pow, one_mul]
  have h1 : t = n ^ (orderOf (n⁻¹ * t)) := by
    calc t = t ^ (orderOf (n⁻¹ * t)) := htk.symm
      _ = (n * (n⁻¹ * t)) ^ (orderOf (n⁻¹ * t)) := by rw [mul_inv_cancel_left]
      _ = n ^ (orderOf (n⁻¹ * t)) * (n⁻¹ * t) ^ (orderOf (n⁻¹ * t)) := hcomm.mul_pow _
      _ = n ^ (orderOf (n⁻¹ * t)) := by rw [pow_orderOf_eq_one, mul_one]
  rw [h1]
  exact pow_mem hn _

end Odd

section Lift

variable {H H' : Type*} [Group H] [Group H'] [Finite H] [Finite H']

theorem exists_isPComponent_map_eq (φ : H →* H') (hφ : ¬ 2 ∣ Nat.card φ.ker) {Y : Subgroup H}
    {N' : Subgroup H'} (hN'Y : N' ≤ Y.map φ) (hN' : IsPComponent 2 (N'.subgroupOf (Y.map φ))) :
    ∃ N : Subgroup H, N ≤ Y ∧ IsPComponent 2 (N.subgroupOf Y) ∧ N.map φ = N' ∧
      Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* ↥N' ⧸ pPrimeCore 2 ↥N') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, -, hiso⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (φ.subgroupMap Y) (φ.subgroupMap_surjective Y)
    (OddQuot.not_two_dvd_card_ker_subgroupMap φ hφ Y)
  obtain ⟨L, hL, hLmap⟩ := hbij.surjOn hN'
  have hLmap' : L.map (φ.subgroupMap Y) = N'.subgroupOf (Y.map φ) := hLmap
  have hsub : (L.map Y.subtype).subgroupOf Y = L :=
    comap_map_eq_self_of_injective Y.subtype_injective L
  refine ⟨L.map Y.subtype, map_subtype_le L, by rw [hsub]; exact hL, ?_, ?_⟩
  · calc (L.map Y.subtype).map φ = (L.map (φ.subgroupMap Y)).map (Y.map φ).subtype := by
          rw [map_map, map_map, OddQuot.subtype_comp_subgroupMap]
      _ = N' := by rw [hLmap', map_subgroupOf_eq_of_le hN'Y]
  · obtain ⟨e, -⟩ := hiso L hL
    let e₁ : ↥(L.map Y.subtype) ≃* ↥L :=
      (L.equivMapOfInjective Y.subtype Y.subtype_injective).symm
    let e₂ : ↥(L.map (φ.subgroupMap Y)) ≃* ↥N' :=
      (MulEquiv.subgroupCongr hLmap').trans (subgroupOfEquivOfLe hN'Y)
    exact ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₁).trans
      (e.trans (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₂))⟩

end Lift

theorem le_of_le_sup_of_le_centralizer {G : Type*} [Group G] {A B Q : Subgroup G} [hA : A.Normal]
    (hQ : Q ≤ A ⊔ B) (hBQ : B ≤ centralizer (Q : Set G)) (hperf : ⁅Q, Q⁆ = Q) : Q ≤ A := by
  rw [← hperf]
  refine (commutator_mono hQ le_rfl).trans ?_
  rw [commutator_le]
  intro x hx q hq
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← normal_mul A B]
    exact hx
  obtain ⟨α, hα, β, hβ, rfl⟩ := Set.mem_mul.mp hx'
  have hβq : β * q = q * β := ((mem_centralizer_iff.mp (hBQ hβ)) q hq).symm
  have heq : ⁅α * β, q⁆ = α * (q * α⁻¹ * q⁻¹) := by
    rw [commutatorElement_def]
    calc α * β * q * (α * β)⁻¹ * q⁻¹ = α * (β * q) * β⁻¹ * α⁻¹ * q⁻¹ := by group
      _ = α * (q * β) * β⁻¹ * α⁻¹ * q⁻¹ := by rw [hβq]
      _ = α * (q * α⁻¹ * q⁻¹) := by group
  rw [heq]
  exact mul_mem hα (hA.conj_mem _ (inv_mem hα) q)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isSubnormal_inf_subgroupOf {A Y C : Subgroup X} (hA : (A.subgroupOf Y).IsSubnormal) :
    ((A ⊓ C).subgroupOf (Y ⊓ C)).IsSubnormal := by
  have h := hA.comap (Subgroup.inclusion (inf_le_left : Y ⊓ C ≤ Y))
  convert h using 1
  ext ⟨x, hx⟩
  simp only [mem_subgroupOf, mem_comap, mem_inf, coe_inclusion]
  exact ⟨fun h => h.1, fun h => ⟨h, hx.2⟩⟩

theorem isPComponent_inf_of_isSubnormal {A Y C N : Subgroup X} (hAY : A ≤ Y)
    (hA : (A.subgroupOf Y).IsSubnormal) (hNA : N ≤ A ⊓ C)
    (hN : IsPComponent 2 (N.subgroupOf (A ⊓ C))) : IsPComponent 2 (N.subgroupOf (Y ⊓ C)) := by
  have hle : A ⊓ C ≤ Y ⊓ C := inf_le_inf_right C hAY
  have hN' : IsPComponent 2 ((N.subgroupOf (Y ⊓ C)).subgroupOf ((A ⊓ C).subgroupOf (Y ⊓ C))) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hle 2 Nat.prime_two).mpr hN
  have hNK : N.subgroupOf (Y ⊓ C) ≤ (A ⊓ C).subgroupOf (Y ⊓ C) := fun x hx =>
    mem_subgroupOf.mpr (hNA (mem_subgroupOf.mp hx))
  rw [OddStandard.Solomon75.isPComponent_two_iff] at hN' ⊢
  refine ⟨Subgroup.IsSubnormal.trans hNK hN'.1 (isSubnormal_inf_subgroupOf hA), ?_⟩
  exact (OddStandard.Solomon75.isTwoGenQuasi_subgroupOf_iff hNK).1 hN'.2

theorem exists_sl2_of_cf (hComp : CFSp4Comp) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {L J₀ Y : Subgroup X}
    (hLie : Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSp 2 p f)
    {t w : X} (htL : t ∈ L) (ht : t * t = 1) (ht1 : t ≠ 1) (hw : w * w = 1) (hw1 : w ≠ 1)
    (htw : t * w = w * t) (hwt : w ≠ t) (hJ0L : J₀ ≤ L) (hJ0t : J₀ ≤ centralizer ({t} : Set X))
    (hYt : L ⊓ centralizer ({t} : Set X) ≤ Y) (hJ0pc : IsPComponent 2 (J₀.subgroupOf Y))
    (hwJ0 : w ∈ J₀) :
    ∃ N : Subgroup X, N ≤ L ⊓ centralizer ({t * w} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (L ⊓ centralizer ({t * w} : Set X))) ∧ t * w ∈ N ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) := by
  have hCF := CFSG.ComponentClassification.CatFactsSp4.cfSp4Prod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set t' : ↥L := ⟨t, htL⟩ with ht'
  set w' : ↥L := ⟨w, hJ0L hwJ0⟩ with hw'
  have ht'2 : t' * t' = 1 := Subtype.ext ht
  have hw'2 : w' * w' = 1 := Subtype.ext hw
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hw'1 : w' ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have htw' : t' * w' = w' * t' := Subtype.ext htw
  have hJ0Lt : J₀ ≤ L ⊓ centralizer ({t} : Set X) := le_inf hJ0L hJ0t
  have hpc1 : IsPComponent 2 (J₀.subgroupOf (L ⊓ centralizer ({t} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0Lt hYt hJ0pc
  have hpc2 : IsPComponent 2 ((J₀.subgroupOf L).subgroupOf (centralizer ({t'} : Set ↥L))) := by
    rw [← inf_centralizer_subgroupOf htL]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hpc1
  have hMt : J₀.subgroupOf L ≤ centralizer ({t'} : Set ↥L) := by
    rw [← inf_centralizer_subgroupOf htL]
    intro v hv
    exact mem_subgroupOf.mpr (hJ0Lt (mem_subgroupOf.mp hv))
  obtain ⟨hMbt, hMbpc⟩ := isPComponent_centralizer_map ht'2 hMt hpc2
  have hne : π w' ≠ π t' := by
    intro h
    have hinj := OddQuot.injOn_of_isPGroup (H := ↥L) (isPGroup_closure_pair hw'2 ht'2 htw'.symm)
    have := hinj (subset_closure (by simp)) (subset_closure (by simp)) h
    exact hwt (congrArg Subtype.val this)
  obtain ⟨Nb, hNbt, hNbpc, htwNb, p', n, hp', hp'2, hn, ⟨eNb⟩⟩ := hCF _ p f hp hp2 hf hLie _ _
    (orderOf_mk_eq_two ht'2 ht'1) (orderOf_mk_eq_two hw'2 hw'1) hne _ hMbt hMbpc
    (mem_map_of_mem _ (mem_subgroupOf.mpr hwJ0))
  have htw'2 : t' * w' * (t' * w') = 1 := by
    rw [show t' * w' * (t' * w') = t' * (w' * t') * w' by group, ← htw',
      show t' * (t' * w') * w' = (t' * t') * (w' * w') by group, ht'2, hw'2, one_mul]
  have htw'1 : t' * w' ≠ 1 := by
    intro h
    apply hwt
    have h1 : w' = t'⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [inv_eq_of_mul_eq_one_right ht'2] at h1
    exact congrArg Subtype.val h1
  have hπtw : π t' * π w' = π (t' * w') := (map_mul π t' w').symm
  rw [hπtw] at hNbt hNbpc htwNb
  have hNbcore : pPrimeCore 2 ↥Nb = ⊥ :=
    hComp _ p f hp hp2 hf hLie _ (orderOf_mk_eq_two htw'2 htw'1) Nb hNbt hNbpc
  have hcen := OddQuot.centralizer_singleton_map_eq (H := ↥L) htw'2
  rw [hcen] at hNbt hNbpc
  obtain ⟨N₁, hN₁X, hN₁pc, hN₁map, ⟨eN₁⟩⟩ := exists_isPComponent_map_eq π
    OddQuot.not_two_dvd_card_ker hNbt hNbpc
  have htwN₁ : t' * w' ∈ N₁ := mem_of_mk_mem hN₁X htw'2 (by rw [hN₁map]; exact htwNb)
  set N := N₁.map L.subtype with hNdef
  have htwL : t * w ∈ L := mul_mem htL (hJ0L hwJ0)
  have hsub : N.subgroupOf L = N₁ := comap_map_eq_self_of_injective L.subtype_injective N₁
  have hcenL : (L ⊓ centralizer ({t * w} : Set X)).subgroupOf L =
      centralizer ({t' * w'} : Set ↥L) := inf_centralizer_subgroupOf htwL
  have hNX : N ≤ L ⊓ centralizer ({t * w} : Set X) := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 : v ∈ (L ⊓ centralizer ({t * w} : Set X)).subgroupOf L := by
      rw [hcenL]
      exact hN₁X hv
    exact mem_subgroupOf.mp h1
  refine ⟨N, hNX, ?_, ⟨t' * w', htwN₁, rfl⟩, p', n, hp', hp'2, hn, ?_⟩
  · have h1 : IsPComponent 2 ((N.subgroupOf L).subgroupOf
        ((L ⊓ centralizer ({t * w} : Set X)).subgroupOf L)) := by
      rw [hsub, hcenL]
      exact hN₁pc
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mp h1
  · let e₀ : ↥N ≃* ↥N₁ := (N₁.equivMapOfInjective L.subtype L.subtype_injective).symm
    exact ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₀).trans
      (eN₁.trans ((QuotientGroup.quotientMulEquivOfEq hNbcore).trans
        (QuotientGroup.quotientBot.trans eNb)))⟩

end Seven

end CFSG.ComponentClassification.GSThmB

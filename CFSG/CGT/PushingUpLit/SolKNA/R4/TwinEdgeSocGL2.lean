module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocDefs
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5GL2
public import CFSG.GH74.Generic.S3.Lem36
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open scoped MatrixGroups commutatorElement

theorem soc_isSylowOf_of_isSylow2In {F : Type} [Group F] [Finite F] {N P : Subgroup F}
    (hP : CFSG.ClassicalInvolution.Asc77.IsSylow2In P N) :
    CFSG.ABGLocalTools.IsSylowOf 2 P N := by
  let Q : Sylow 2 N :=
    { toSubgroup := P.subgroupOf N
      isPGroup' := hP.2.1.comap_subtype
      is_maximal' := by
        intro Q' hQ' hle
        have hPQ : P ≤ Q'.map N.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hP.1]
          exact Subgroup.map_mono hle
        have h := hP.2.2 (Q'.map N.subtype) (Subgroup.map_subtype_le _) (hQ'.map _) hPQ
        rw [← Subgroup.comap_map_eq_self_of_injective N.subtype_injective Q', h]
        rfl }
  exact ⟨Q, by
    show (P.subgroupOf N).map N.subtype = P
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP.1]⟩

theorem soc_eq_one_of_cubeKer {K : Type} [Field K] {H : Subgroup (GL (Fin 2) K)} {X : Type} [Group X]
    {π : H →* X} (hk : CubeKer π) {a : H} (ha : π a = 1) {k : ℕ} (hpow : a ^ (2 ^ k) = 1) :
    a = 1 := by
  obtain ⟨ω, hω3, hω⟩ := hk a ha
  have h3 : a ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hω, ← map_pow, hω3, map_one]
    rfl
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : a ^ Nat.gcd 3 (2 ^ k) = 1 := (pow_gcd_eq_one (a := a)).mpr ⟨h3, hpow⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  exact h1

theorem soc_isCyclic_of_le_comap {K : Type} [Field K] {H : Subgroup (GL (Fin 2) K)} {F : Type}
    [Group F] [Finite F] {π : H →* F} (hk : CubeKer π) {N P : Subgroup F}
    (hP : CFSG.ClassicalInvolution.Asc77.IsSylow2In P N) (hPc : IsCyclic P) {V : Subgroup H}
    (hV : V ≤ N.comap π) (hp : IsPGroup 2 V) : IsCyclic V := by
  have hVN : V.map π ≤ N := Subgroup.map_le_iff_le_comap.mpr hV
  have hcycN : IsCyclic (V.map π) :=
    CFSG.GH74.Generic.S3.isCyclic_of_isPGroup_le (soc_isSylowOf_of_isSylow2In hP) hPc hVN (hp.map π)
  let ψ : V →* V.map π :=
    { toFun := fun x => ⟨π (x : H), Subgroup.mem_map_of_mem π x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hπa : π (a : H) = 1 := congrArg Subtype.val ha
    obtain ⟨k, hk'⟩ := hp a
    have hpow : (a : H) ^ (2 ^ k) = 1 := by
      rw [← Subgroup.coe_pow, hk', Subgroup.coe_one]
    exact Subtype.ext (soc_eq_one_of_cubeKer hk hπa hpow)
  exact isCyclic_of_injective ψ hinj

@[expose] def socScalarPart {K : Type} [Field K] (H : Subgroup (GL (Fin 2) K)) : Subgroup H :=
  (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range.subgroupOf H

theorem soc_isCyclic_scalarPart {K : Type} [Field K] [Finite K] (H : Subgroup (GL (Fin 2) K)) :
    IsCyclic (socScalarPart H) := by
  have hscinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K) :=
    fun a b h => scalar_injective h
  have hR : IsCyclic ↥(Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range :=
    isCyclic_of_surjective (MonoidHom.ofInjective hscinj).toMonoidHom
      (MulEquiv.surjective (MonoidHom.ofInjective hscinj))
  let f : socScalarPart H →* ↥(Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range :=
    { toFun := fun x => ⟨(x.1 : GL (Fin 2) K), Subgroup.mem_subgroupOf.mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  exact isCyclic_of_injective f hf

theorem soc_commute_of_center {H : Type} [Group H] {S M : Subgroup H} [S.Normal] [M.Normal]
    (hQ : CFSG.IsQuasisimple S) (hD : M.subgroupOf S ≤ Subgroup.center S) {m : H} (hm : m ∈ M) :
    ∀ s ∈ S, m * s = s * m := by
  have hmemS : ∀ s : S, ⁅m, (s : H)⁆ ∈ S := fun s => by
    rw [commutatorElement_def]
    exact S.mul_mem (Subgroup.Normal.conj_mem inferInstance (s : H) s.2 m) (S.inv_mem s.2)
  have hmemM : ∀ s : S, ⁅m, (s : H)⁆ ∈ M := fun s => by
    have h1 : (s : H) * m⁻¹ * (s : H)⁻¹ ∈ M :=
      Subgroup.Normal.conj_mem inferInstance m⁻¹ (M.inv_mem hm) (s : H)
    have e : ⁅m, (s : H)⁆ = m * ((s : H) * m⁻¹ * (s : H)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact M.mul_mem hm h1
  have hcen : ∀ s : S, (⟨⁅m, (s : H)⁆, hmemS s⟩ : S) ∈ Subgroup.center S := fun s =>
    hD (Subgroup.mem_subgroupOf.mpr (hmemM s))
  have hkey : ∀ s t : S, ⁅m, (s : H)⁆ * ⁅m, (t : H)⁆ = ⁅m, (s : H) * (t : H)⁆ := by
    intro s t
    have hc : (s : H)⁻¹ * (m * (t : H) * m⁻¹ * (t : H)⁻¹) =
        (m * (t : H) * m⁻¹ * (t : H)⁻¹) * (s : H)⁻¹ :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen t) s⁻¹)
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc m * (s : H) * m⁻¹ * (s : H)⁻¹ * (m * (t : H) * m⁻¹ * (t : H)⁻¹)
        = m * (s : H) * m⁻¹ * ((s : H)⁻¹ * (m * (t : H) * m⁻¹ * (t : H)⁻¹)) := by group
      _ = m * (s : H) * m⁻¹ * ((m * (t : H) * m⁻¹ * (t : H)⁻¹) * (s : H)⁻¹) := by rw [hc]
      _ = m * ((s : H) * (t : H)) * m⁻¹ * ((s : H) * (t : H))⁻¹ := by group
  let ψ : S →* ↥(Subgroup.center S) :=
    { toFun := fun s => ⟨⟨⁅m, (s : H)⁆, hmemS s⟩, hcen s⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun s t => by
        apply Subtype.ext
        apply Subtype.ext
        exact (hkey s t).symm }
  have hperf : commutator (↥S) = ⊤ := hQ.1.commutator_eq_top
  have htop : (⊤ : Subgroup (↥S)) ≤ ψ.ker := by
    rw [← hperf]
    exact Abelianization.commutator_subset_ker ψ
  intro s hs
  have hψ : ψ ⟨s, hs⟩ = 1 := MonoidHom.mem_ker.mp (htop (Subgroup.mem_top _))
  have h1 : ⁅m, s⁆ = 1 := congrArg (fun x : ↥(Subgroup.center S) => ((x : S) : H)) hψ
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem soc_mem_scalar_of_mem_comap {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 2) K)}
    {F : Type} [Group F] [Finite F] {z : F} {π : H →* F}
    (hrange : π.range = Subgroup.centralizer ({z} : Set F)) (hk : CubeKer π)
    (hcs : SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : ringChar F₀ ≠ 2)
    (h4 : 4 ≤ Nat.card F₀) (eJ : slPart H ≃* SL(2, F₀))
    {N P : Subgroup F} (hN : N ≤ Subgroup.centralizer ({z} : Set F))
    (hNn : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (N : Set F))
    (hP : CFSG.ClassicalInvolution.Asc77.IsSylow2In P N) (hPc : IsCyclic P) {m : H}
    (hm : π m ∈ N) : ∃ c : Kˣ, (m : GL (Fin 2) K) = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  obtain ⟨M, hM⟩ : ∃ M : Subgroup H, M = N.comap π := ⟨_, rfl⟩
  have hmemM : ∀ x : H, x ∈ M ↔ π x ∈ N := fun x => by
    rw [hM]
    exact Iff.rfl
  have hCπ : ∀ g : H, π g ∈ Subgroup.centralizer ({z} : Set F) := fun g => by
    rw [← hrange]
    exact ⟨g, rfl⟩
  have hMn : M.Normal := ⟨fun n hn g => by
    rw [hmemM] at hn
    rw [hmemM, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hNn (hCπ g)) (π n)).mp hn⟩
  have hSn : (slPart H).Normal := MonoidHom.normal_ker _
  have hacyc : ∀ V : Subgroup H, V ≤ M → IsPGroup 2 V → IsCyclic V := fun V hV hp =>
    soc_isCyclic_of_le_comap hk hP hPc (by rw [← hM]; exact hV) hp
  have hnot : ¬ slPart H ≤ M := by
    intro hle
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨Q⟩ : Nonempty (Sylow 2 M) := inferInstance
    have hS : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup M).map M.subtype) M := ⟨Q, rfl⟩
    have hSp : IsPGroup 2 ↥((Q : Subgroup M).map M.subtype) := Q.isPGroup'.map M.subtype
    exact CFSG.GH74.Generic.S3.false_of_sl2_le_cyclic_sylow hS
      (hacyc _ (Subgroup.map_subtype_le _) hSp) hle hF₀ eJ.symm
  have hQS : CFSG.IsQuasisimple ↥(slPart H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4)
  have hDc : M.subgroupOf (slPart H) ≤ Subgroup.center ↥(slPart H) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQS
        (Subgroup.Normal.subgroupOf hMn (slPart H)) with h | h
    · exfalso
      apply hnot
      intro s hs
      have hs' : (⟨s, hs⟩ : ↥(slPart H)) ∈ M.subgroupOf (slPart H) := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hs'
    · exact h
  have hcomm : ∀ s ∈ slPart H, m * s = s * m :=
    soc_commute_of_center hQS hDc ((hmemM m).mpr hm)
  exact hcs (m : GL (Fin 2) K) (fun B hB => congrArg Subtype.val (hcomm B hB))

theorem soc_exists_cyclic_of_gl2 {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 2) K)}
    {F : Type} [Group F] [Finite F] {z : F} {π : H →* F}
    (hrange : π.range = Subgroup.centralizer ({z} : Set F)) (hk : CubeKer π)
    (hcs : SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : ringChar F₀ ≠ 2)
    (h4 : 4 ≤ Nat.card F₀) (eJ : slPart H ≃* SL(2, F₀)) :
    ∃ A : Subgroup F, IsCyclic A ∧ ∀ N P : Subgroup F,
      N ≤ Subgroup.centralizer ({z} : Set F) →
      Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (N : Set F) →
      CFSG.ClassicalInvolution.Asc77.IsSylow2In P N → IsCyclic P → N ≤ A := by
  have hHsc : IsCyclic (socScalarPart H) := soc_isCyclic_scalarPart H
  refine ⟨(π.comp (socScalarPart H).subtype).range, ?_, ?_⟩
  · exact isCyclic_of_surjective (π.comp (socScalarPart H).subtype).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  · intro N P hN hNn hP hPc n hn
    have hnr : n ∈ π.range := by
      rw [hrange]
      exact hN hn
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hnr
    obtain ⟨c, hc⟩ := soc_mem_scalar_of_mem_comap hrange hk hcs hF₀ h4 eJ hN hNn hP hPc
      (m := m) (by rw [hm]; exact hn)
    exact MonoidHom.mem_range.mpr ⟨⟨m, Subgroup.mem_subgroupOf.mpr
      (MonoidHom.mem_range.mpr ⟨c, hc.symm⟩)⟩, hm⟩

theorem socleCyc4_of_gl2 {F : Type} [Group F] [Finite F] {K : Type} [Field K] [Finite K]
    {z : F} (hz : orderOf z = 2) {H : Subgroup (GL (Fin 2) K)} (π : H →* F)
    (hrange : π.range = Subgroup.centralizer ({z} : Set F)) (hk : CubeKer π)
    (hcs : SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : ringChar F₀ ≠ 2)
    (h4 : 4 ≤ Nat.card F₀) (eJ : slPart H ≃* SL(2, F₀)) :
    ∀ N₁ N₂ P₁ P₂ : Subgroup F,
      N₁ ≤ Subgroup.centralizer {z} → N₂ ≤ Subgroup.centralizer {z} →
      Subgroup.centralizer {z} ≤ Subgroup.normalizer (N₁ : Set F) →
      Subgroup.centralizer {z} ≤ Subgroup.normalizer (N₂ : Set F) →
      CFSG.ClassicalInvolution.Asc77.IsSylow2In P₁ N₁ →
      CFSG.ClassicalInvolution.Asc77.IsSylow2In P₂ N₂ →
      IsCyclic P₁ → IsCyclic P₂ → 4 ≤ Nat.card P₁ → 4 ≤ Nat.card P₂ → ∃ u ∈ P₁ ⊓ P₂, orderOf u = 4 := by
  obtain ⟨A, hA, hAN⟩ := soc_exists_cyclic_of_gl2 hrange hk hcs hF₀ h4 eJ
  intro N₁ N₂ P₁ P₂ hN₁ hN₂ hC₁ hC₂ hP₁ hP₂ hc₁ hc₂ hn₁ hn₂
  exact soc_exists_common_orderOf_four hA (hP₁.1.trans (hAN N₁ P₁ hN₁ hC₁ hP₁ hc₁))
    (hP₂.1.trans (hAN N₂ P₂ hN₂ hC₂ hP₂ hc₂)) hP₁.2.1 hP₂.2.1 hc₁ hc₂ hn₁ hn₂

end CFSG.CGT.PushingUpLit.SolKNA.R4

module

public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral

universe u

variable {H : Type u} [Group H] {n : ℕ}

section Elements

theorem ambientHom_symm_apply (S : Subgroup H) (f : SemidihedralGroup n ≃* S) (x : H)
    (hx : x ∈ S) : FocalFusion.ambientHom n S f (f.symm ⟨x, hx⟩) = x := by
  change ((f (f.symm ⟨x, hx⟩) : S) : H) = x
  rw [MulEquiv.apply_symm_apply]

theorem ambientHom_symm (S : Subgroup H) (f : SemidihedralGroup n ≃* S) (y : S) :
    FocalFusion.ambientHom n S f (f.symm y) = y := by
  change ((f (f.symm y) : S) : H) = y
  rw [MulEquiv.apply_symm_apply]

theorem exists_ambientHom_eq (S : Subgroup H) (f : SemidihedralGroup n ≃* S) (x : H)
    (hx : x ∈ S) : ∃ y, FocalFusion.ambientHom n S f y = x :=
  ⟨_, ambientHom_symm_apply S f x hx⟩

theorem orderOf_ambientHom (S : Subgroup H) (f : SemidihedralGroup n ≃* S)
    (x : SemidihedralGroup n) : orderOf (FocalFusion.ambientHom n S f x) = orderOf x :=
  orderOf_injective _ (FocalFusion.ambientHom_injective n S f) x

theorem conj_ambient_z (hn : 4 ≤ n) (S : Subgroup H) (f : SemidihedralGroup n ≃* S) (x : H)
    (hx : x ∈ S) :
    x * FocalFusion.ambientHom n S f (z n) * x⁻¹ = FocalFusion.ambientHom n S f (z n) := by
  obtain ⟨y, rfl⟩ := exists_ambientHom_eq S f x hx
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  have hc := Subgroup.mem_center_iff.mp (z_mem_center n hn) y
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem conj_mem_map_ambientHom (S : Subgroup H) (f : SemidihedralGroup n ≃* S)
    (P : Subgroup (SemidihedralGroup n)) (hP : P.Normal) (x : H) (hx : x ∈ S) (w : H)
    (hw : w ∈ P.map (FocalFusion.ambientHom n S f)) :
    x * w * x⁻¹ ∈ P.map (FocalFusion.ambientHom n S f) := by
  obtain ⟨y, rfl⟩ := exists_ambientHom_eq S f x hx
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  rw [← map_inv, ← map_mul, ← map_mul]
  exact ⟨_, hP.conj_mem w₀ hw₀ y, rfl⟩

theorem ambientHom_mem_map_iff (S : Subgroup H) (f : SemidihedralGroup n ≃* S)
    (P : Subgroup (SemidihedralGroup n)) (x : SemidihedralGroup n) :
    FocalFusion.ambientHom n S f x ∈ P.map (FocalFusion.ambientHom n S f) ↔ x ∈ P :=
  Subgroup.mem_map_iff_mem (FocalFusion.ambientHom_injective n S f)

theorem map_conj_one (P : Subgroup H) : P.map (MulAut.conj (1 : H)).toMonoidHom = P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x, hx, by simp⟩

theorem le_normalizer_zpowers {Q : Subgroup H} {y : H}
    (h : ∀ q ∈ Q, q * y * q⁻¹ ∈ Subgroup.zpowers y) :
    Q ≤ Subgroup.normalizer (Subgroup.zpowers y : Set H) := by
  have hpow : ∀ q ∈ Q, ∀ x ∈ Subgroup.zpowers y, q * x * q⁻¹ ∈ Subgroup.zpowers y := by
    intro q hq x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact Subgroup.zpow_mem _ (h q hq) k
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hpow q hq x, fun hx => ?_⟩
  have h' := hpow q⁻¹ (Q.inv_mem hq) _ hx
  have heq : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
  rwa [heq] at h'

theorem quaternion_conj_mem_zpowers {Q : Subgroup H} (hQ : Nonempty (Q ≃* QuaternionGroup 2))
    {y : H} (hyQ : y ∈ Q) (hy : orderOf y = 4) (q : H) (hq : q ∈ Q) :
    q * y * q⁻¹ ∈ Subgroup.zpowers y := by
  obtain ⟨e⟩ := hQ
  let P : Subgroup Q := Subgroup.zpowers ⟨y, hyQ⟩
  have hP : Nat.card P = 4 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hy]
  have hindex : P.index = 2 := by
    have h := Subgroup.card_mul_index P
    rw [hP, Local.card_of_equiv e] at h
    omega
  have hN := Subgroup.normal_of_index_eq_two hindex
  have hmem := hN.conj_mem ⟨y, hyQ⟩ (Subgroup.mem_zpowers _) ⟨q, hq⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have h := congrArg Subtype.val hk
  simpa only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem exists_mulAut_eq_or_eq_inv {Q : Type*} [Group Q] (e : Q ≃* QuaternionGroup 2)
    (y v : Q) (hy : y ^ 2 ≠ 1) (hv : v ^ 2 ≠ 1) : ∃ ψ : MulAut Q, ψ y = v ∨ ψ y = v⁻¹ := by
  classical
  obtain ⟨-, -, ⟨ρ, hρ, hsurj, -⟩, -⟩ := Local.quaternionEight_automorphism_action ⟨e⟩
  let Y : {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} :=
    ⟨Subgroup.zpowers y, (Local.cyclicFour_iff e _).mpr ⟨y, hy, rfl⟩⟩
  let V : {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} :=
    ⟨Subgroup.zpowers v, (Local.cyclicFour_iff e _).mpr ⟨v, hv, rfl⟩⟩
  obtain ⟨ψ, hψ⟩ := hsurj (Equiv.swap Y V)
  refine ⟨ψ, Local.eq_or_eq_inv_of_mem_zpowers e ?_ ?_⟩
  · have h1 := hρ ψ Y
    rw [hψ, Equiv.swap_apply_left] at h1
    have hmem : ψ y ∈ (Subgroup.zpowers y).map ψ.toMonoidHom :=
      ⟨y, Subgroup.mem_zpowers y, rfl⟩
    have h2 : (V : Subgroup Q) = (Subgroup.zpowers y).map ψ.toMonoidHom := h1
    rw [← h2] at hmem
    exact hmem
  · rw [← map_pow]
    exact (MulEquiv.map_ne_one_iff ψ).mpr hy

end Elements

section Automizers

variable [Finite H]

theorem exists_mem_normalizer_qdFour (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S)
    (ha : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n))) :
    ∃ h ∈ Subgroup.normalizer (qdFour (S : Subgroup H) f : Set H),
      h * FocalFusion.ambientHom n (S : Subgroup H) f (s n) * h⁻¹ =
        FocalFusion.ambientHom n (S : Subgroup H) f (z n) := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  set T := qdFour (S : Subgroup H) f with hT
  have : IsKleinFour T := qdFour_isKleinFour hn _ f
  have hsT : ι (s n) ∈ T := ⟨s n, s_mem_sdFourSubgroup n, rfl⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  let C := Subgroup.centralizer ({ι (z n)} : Set H)
  have hcomm : ∀ x : H, x * ι (z n) * x⁻¹ = ι (z n) → x ∈ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * ι (z n) = x * ι (z n) * x⁻¹ * x := by group
      _ = ι (z n) * x := by rw [hx]
  have hSC : (S : Subgroup H) ≤ C := fun x hx =>
    hcomm x (conj_ambient_z hn (S : Subgroup H) f x hx)
  have hWC : T.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hts : t * ι (s n) = ι (s n) * t := Local.kleinFour_mul_comm T ht hsT
    change g * t * g⁻¹ * ι (z n) = ι (z n) * (g * t * g⁻¹)
    rw [← hg]
    calc g * t * g⁻¹ * (g * ι (s n) * g⁻¹) = g * (t * ι (s n)) * g⁻¹ := by group
      _ = g * (ι (s n) * t) * g⁻¹ := by rw [hts]
      _ = g * ι (s n) * g⁻¹ * (g * t * g⁻¹) := by group
  have hW2 : IsPGroup 2 (T.map (MulAut.conj g).toMonoidHom) :=
    (S.isPGroup'.to_le (qdFour_le _ f)).map _
  obtain ⟨c, hcC, hcW⟩ := exists_conj_le_sylow C S hSC _ hWC hW2
  rw [map_conj_mul] at hcW
  have : IsKleinFour (T.map (MulAut.conj (c * g)).toMonoidHom) :=
    Local.isKleinFour_of_mulEquiv (T.equivMapOfInjective _ (MulAut.conj (c * g)).injective)
  obtain ⟨w, hwS, hw⟩ := exists_conj_eq_qdFour hn (S : Subgroup H) f _ hcW
  have hcz : c * ι (z n) * c⁻¹ = ι (z n) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hcC
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨w⁻¹ * (c * g), mem_normalizer_of_map_conj_eq ?_, ?_⟩
  · rw [← map_conj_mul, hw, map_conj_mul, inv_mul_cancel, map_conj_one]
  · calc w⁻¹ * (c * g) * ι (s n) * (w⁻¹ * (c * g))⁻¹ =
          w⁻¹ * (c * (g * ι (s n) * g⁻¹) * c⁻¹) * w⁻¹⁻¹ := by group
      _ = w⁻¹ * ι (z n) * w⁻¹⁻¹ := by rw [hg, hcz]
      _ = ι (z n) := conj_ambient_z hn (S : Subgroup H) f _ ((S : Subgroup H).inv_mem hwS)

theorem qdFour_automizer_alternatives (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    let T := qdFour (S : Subgroup H) f
    let AutS := (((S : Subgroup H) ⊓ Subgroup.normalizer (T : Set H)).subgroupOf
      (Subgroup.normalizer (T : Set H))).map T.normalizerMonoidHom
    Nat.card AutS = 2 ∧ (T.normalizerMonoidHom.range = AutS ∨ T.normalizerMonoidHom.range = ⊤) := by
  intro T AutS
  have hK : IsKleinFour T := qdFour_isKleinFour hn _ f
  obtain ⟨-, -, -, -, -, -, -, hfour, -⟩ :=
    Local.four_and_quaternion_eight_local_normalizer_quotients n hn S f T (qdFour_le _ f)
      (Or.inl hK)
  obtain ⟨-, -, hS2, halt⟩ := hfour hK
  refine ⟨hS2, ?_⟩
  rcases halt with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem automizerIndex_qdFour_eq_six (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (ha : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n))) :
    automizerIndex (qdFour (S : Subgroup H) f) = 6 := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  set T := qdFour (S : Subgroup H) f with hT
  have hK : IsKleinFour T := qdFour_isKleinFour hn _ f
  have hsT : ι (s n) ∈ T := ⟨s n, s_mem_sdFourSubgroup n, rfl⟩
  obtain ⟨-, halt⟩ := qdFour_automizer_alternatives hn S f
  rcases halt with hGS | htop
  · exfalso
    obtain ⟨h, hhN, hhs⟩ := exists_mem_normalizer_qdFour hn S f ha
    have hmem : T.normalizerMonoidHom ⟨h, hhN⟩ ∈ T.normalizerMonoidHom.range := ⟨_, rfl⟩
    rw [hGS] at hmem
    obtain ⟨x, hx, hxh⟩ := hmem
    have hxS : (x : H) ∈ (S : Subgroup H) := (Subgroup.mem_subgroupOf.mp hx).1
    have heq := congrArg (fun φ : MulAut T => ((φ ⟨ι (s n), hsT⟩ : T) : H)) hxh
    change (x : H) * ι (s n) * (x : H)⁻¹ = h * ι (s n) * h⁻¹ at heq
    rw [hhs] at heq
    have hsz : ι (s n) = ι (z n) := by
      calc ι (s n) = (x : H)⁻¹ * ((x : H) * ι (s n) * (x : H)⁻¹) * (x : H)⁻¹⁻¹ := by group
        _ = (x : H)⁻¹ * ι (z n) * (x : H)⁻¹⁻¹ := by rw [heq]
        _ = ι (z n) := conj_ambient_z hn (S : Subgroup H) f _ ((S : Subgroup H).inv_mem hxS)
    exact s_ne_z hn (FocalFusion.ambientHom_injective n _ f hsz)
  · rw [automizerIndex_eq_card_range, htop, Subgroup.card_top,
      (Local.kleinFour_automorphism_action (V := T)).2.1]

theorem isConj_of_automizerIndex_qdFour_ne_two (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) (h2 : automizerIndex (qdFour (S : Subgroup H) f) ≠ 2) :
    IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n)) := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  set T := qdFour (S : Subgroup H) f with hT
  have hK : IsKleinFour T := qdFour_isKleinFour hn _ f
  have hsT : ι (s n) ∈ T := ⟨s n, s_mem_sdFourSubgroup n, rfl⟩
  have hzT : ι (z n) ∈ T := ⟨z n, z_mem_sdFourSubgroup n, rfl⟩
  obtain ⟨hS2, halt⟩ := qdFour_automizer_alternatives hn S f
  rcases halt with hGS | htop
  · exact absurd (by rw [automizerIndex_eq_card_range, hGS, hS2]) h2
  · classical
    obtain ⟨e, he⟩ := (Local.kleinFour_automorphism_action (V := T)).1
    have hs1 : (⟨ι (s n), hsT⟩ : T) ≠ 1 := by
      intro h
      have h' := congrArg Subtype.val h
      change ι (s n) = 1 at h'
      rw [← map_one ι] at h'
      have h'' := FocalFusion.ambientHom_injective n _ f h'
      have ho := orderOf_s n (by omega)
      rw [h'', orderOf_one] at ho
      omega
    have hz1 : (⟨ι (z n), hzT⟩ : T) ≠ 1 := by
      intro h
      have h' := congrArg Subtype.val h
      change ι (z n) = 1 at h'
      rw [← map_one ι] at h'
      exact z_ne_one n (by omega) (FocalFusion.ambientHom_injective n _ f h')
    let sT : {x : T // x ≠ 1} := ⟨⟨ι (s n), hsT⟩, hs1⟩
    let zT : {x : T // x ≠ 1} := ⟨⟨ι (z n), hzT⟩, hz1⟩
    let ψ : MulAut T := e.symm (Equiv.swap sT zT)
    have hψ : ψ ⟨ι (s n), hsT⟩ = ⟨ι (z n), hzT⟩ := by
      have h1 := he ψ sT
      rw [MulEquiv.apply_symm_apply, Equiv.swap_apply_left] at h1
      exact h1.symm
    have hψmem : ψ ∈ T.normalizerMonoidHom.range := by
      rw [htop]
      exact Subgroup.mem_top ψ
    obtain ⟨h, hh⟩ := hψmem
    refine isConj_iff.mpr ⟨h, ?_⟩
    have h1 := congrArg (fun φ : MulAut T => ((φ ⟨ι (s n), hsT⟩ : T) : H)) hh
    change (h : H) * ι (s n) * (h : H)⁻¹ = ((ψ ⟨ι (s n), hsT⟩ : T) : H) at h1
    rw [h1, hψ]

theorem automizerIndex_qdFour_eq_two (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (ha : ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n))) :
    automizerIndex (qdFour (S : Subgroup H) f) = 2 := by
  by_contra h
  exact ha (isConj_of_automizerIndex_qdFour_ne_two hn S f h)

theorem exists_mem_normalizer_qdQuaternion (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S)
    (hb : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) :
    ∃ h ∈ Subgroup.normalizer (qdQuaternion (S : Subgroup H) f : Set H),
      h * FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n) * h⁻¹ ∈
        (rotationSubgroup n).map (FocalFusion.ambientHom n (S : Subgroup H) f) := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  set Q := qdQuaternion (S : Subgroup H) f with hQ
  have hQ8 := qdQuaternion_equiv hn (S : Subgroup H) f
  have hyQ : ι (r n * s n) ∈ Q := ⟨r n * s n, rs_mem_sdQuaternionEight n, rfl⟩
  have hy4 : orderOf (ι (r n * s n)) = 4 := by
    rw [orderOf_ambientHom, orderOf_rs hn]
  obtain ⟨g, hg⟩ := isConj_iff.mp hb
  let V := (Subgroup.zpowers (r n ^ (2 ^ (n - 3)))).map ι
  have hVeq : V = Subgroup.zpowers (ι (r n ^ (2 ^ (n - 3)))) := MonoidHom.map_zpowers _ _
  let NV := Subgroup.normalizer (Subgroup.zpowers (ι (r n ^ (2 ^ (n - 3)))) : Set H)
  have hVnormal := zpowers_sdV_normal (n := n) hn
  have hSN : (S : Subgroup H) ≤ NV := by
    apply le_normalizer_zpowers
    intro x hx
    rw [← hVeq]
    exact conj_mem_map_ambientHom (S : Subgroup H) f _ hVnormal x hx _
      ⟨_, Subgroup.mem_zpowers _, rfl⟩
  have hWN : Q.map (MulAut.conj g).toMonoidHom ≤ NV := by
    apply le_normalizer_zpowers
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (quaternion_conj_mem_zpowers hQ8 hyQ hy4 q hq)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    change ι (r n ^ (2 ^ (n - 3))) ^ k =
      g * q * g⁻¹ * ι (r n ^ (2 ^ (n - 3))) * (g * q * g⁻¹)⁻¹
    rw [← hg]
    calc (g * ι (r n * s n) * g⁻¹) ^ k = g * ι (r n * s n) ^ k * g⁻¹ := by
          rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
      _ = g * (q * ι (r n * s n) * q⁻¹) * g⁻¹ := by rw [hk]
      _ = g * q * g⁻¹ * (g * ι (r n * s n) * g⁻¹) * (g * q * g⁻¹)⁻¹ := by group
  have hW2 : IsPGroup 2 (Q.map (MulAut.conj g).toMonoidHom) :=
    (S.isPGroup'.to_le (qdQuaternion_le _ f)).map _
  obtain ⟨c, hcN, hcW⟩ := exists_conj_le_sylow NV S hSN _ hWN hW2
  rw [map_conj_mul] at hcW
  obtain ⟨eQ⟩ := hQ8
  have hQ' : Nonempty (Q.map (MulAut.conj (c * g)).toMonoidHom ≃* QuaternionGroup 2) :=
    ⟨(Q.equivMapOfInjective _ (MulAut.conj (c * g)).injective).symm.trans eQ⟩
  obtain ⟨w, hwS, hw⟩ := exists_conj_eq_qdQuaternion hn (S : Subgroup H) f _ hcW hQ'
  refine ⟨w⁻¹ * (c * g), mem_normalizer_of_map_conj_eq ?_, ?_⟩
  · rw [← map_conj_mul, hw, map_conj_mul, inv_mul_cancel, map_conj_one]
  · have hcv : c * ι (r n ^ (2 ^ (n - 3))) * c⁻¹ ∈ V := by
      rw [hVeq]
      exact (Subgroup.mem_normalizer_iff.mp hcN _).mp (Subgroup.mem_zpowers _)
    have hVR : V ≤ (rotationSubgroup n).map ι :=
      Subgroup.map_mono (Subgroup.zpowers_le.mpr (sdV_mem_rotationSubgroup n))
    have hw' := conj_mem_map_ambientHom (S : Subgroup H) f _
      (rotationSubgroup_normal n (by omega)) _ ((S : Subgroup H).inv_mem hwS) _ (hVR hcv)
    have heq : w⁻¹ * (c * g) * ι (r n * s n) * (w⁻¹ * (c * g))⁻¹ =
        w⁻¹ * (c * ι (r n ^ (2 ^ (n - 3))) * c⁻¹) * w⁻¹⁻¹ := by
      rw [← hg]
      group
    rw [heq]
    exact hw'

theorem qdQuaternion_automizer_alternatives (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    let Q := qdQuaternion (S : Subgroup H) f
    let AutS := (((S : Subgroup H) ⊓ Subgroup.normalizer (Q : Set H)).subgroupOf
      (Subgroup.normalizer (Q : Set H))).map Q.normalizerMonoidHom
    Nat.card AutS = 8 ∧ (Q.normalizerMonoidHom.range = AutS ∨ Q.normalizerMonoidHom.range = ⊤) := by
  intro Q AutS
  have hQ8 := qdQuaternion_equiv hn (S : Subgroup H) f
  obtain ⟨-, -, -, -, -, -, -, -, hquat⟩ :=
    Local.four_and_quaternion_eight_local_normalizer_quotients n hn S f Q (qdQuaternion_le _ f)
      (Or.inr hQ8)
  obtain ⟨-, hS8, halt, -⟩ := hquat hQ8
  refine ⟨hS8, ?_⟩
  rcases halt with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem outerAutomizerIndex_qdQuaternion_mul_four (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    outerAutomizerIndex (qdQuaternion (S : Subgroup H) f) * 4 =
      Nat.card (qdQuaternion (S : Subgroup H) f).normalizerMonoidHom.range := by
  have hQ8 := qdQuaternion_equiv hn (S : Subgroup H) f
  rw [← outerAutomizerIndex_mul_card_inner,
    (Local.quaternionEight_automorphism_action hQ8).2.2.2.1]

theorem outerAutomizerIndex_qdQuaternion_eq_six (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S)
    (hb : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) :
    outerAutomizerIndex (qdQuaternion (S : Subgroup H) f) = 6 := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  set Q := qdQuaternion (S : Subgroup H) f with hQ
  have hQ8 := qdQuaternion_equiv hn (S : Subgroup H) f
  have hyQ : ι (r n * s n) ∈ Q := ⟨r n * s n, rs_mem_sdQuaternionEight n, rfl⟩
  have h4 := outerAutomizerIndex_qdQuaternion_mul_four hn S f
  rw [← hQ] at h4
  obtain ⟨-, halt⟩ := qdQuaternion_automizer_alternatives hn S f
  rcases halt with hGS | htop
  · exfalso
    obtain ⟨h, hhN, hhy⟩ := exists_mem_normalizer_qdQuaternion hn S f hb
    have hmem : Q.normalizerMonoidHom ⟨h, hhN⟩ ∈ Q.normalizerMonoidHom.range := ⟨_, rfl⟩
    rw [hGS] at hmem
    obtain ⟨x, hx, hxh⟩ := hmem
    have hxS : (x : H) ∈ (S : Subgroup H) := (Subgroup.mem_subgroupOf.mp hx).1
    have heq := congrArg (fun φ : MulAut Q => ((φ ⟨ι (r n * s n), hyQ⟩ : Q) : H)) hxh
    change (x : H) * ι (r n * s n) * (x : H)⁻¹ = h * ι (r n * s n) * h⁻¹ at heq
    rw [← heq] at hhy
    have hback := conj_mem_map_ambientHom (S : Subgroup H) f _
      (rotationSubgroup_normal n (by omega)) _ ((S : Subgroup H).inv_mem hxS) _ hhy
    have hy : ι (r n * s n) ∈ (rotationSubgroup n).map ι := by
      have h' : (x : H)⁻¹ * ((x : H) * ι (r n * s n) * (x : H)⁻¹) * (x : H)⁻¹⁻¹ =
          ι (r n * s n) := by group
      rwa [h'] at hback
    rw [ambientHom_mem_map_iff] at hy
    exact rs_not_mem_rotationSubgroup hn hy
  · rw [htop, Subgroup.card_top, (Local.quaternionEight_automorphism_action hQ8).2.1] at h4
    omega

theorem isConj_of_outerAutomizerIndex_qdQuaternion_ne_two (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S)
    (h2 : outerAutomizerIndex (qdQuaternion (S : Subgroup H) f) ≠ 2) :
    IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3)))) := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  set Q := qdQuaternion (S : Subgroup H) f with hQ
  have hQ8 := qdQuaternion_equiv hn (S : Subgroup H) f
  have hyQ : ι (r n * s n) ∈ Q := ⟨r n * s n, rs_mem_sdQuaternionEight n, rfl⟩
  have hvQ : ι (r n ^ (2 ^ (n - 3))) ∈ Q :=
    ⟨r n ^ (2 ^ (n - 3)), sdV_mem_sdQuaternionEight n, rfl⟩
  have h4 := outerAutomizerIndex_qdQuaternion_mul_four hn S f
  rw [← hQ] at h4
  obtain ⟨hS8, halt⟩ := qdQuaternion_automizer_alternatives hn S f
  rcases halt with hGS | htop
  · rw [hGS, hS8] at h4
    omega
  · obtain ⟨eQ⟩ := hQ8
    have hsq : ∀ x : Q, orderOf (x : H) = 4 → x ^ 2 ≠ 1 := by
      intro x hx h
      have hdvd := orderOf_dvd_of_pow_eq_one h
      rw [Subgroup.orderOf_coe] at hx
      rw [hx] at hdvd
      norm_num at hdvd
    have hy2 := hsq ⟨ι (r n * s n), hyQ⟩ (by rw [orderOf_ambientHom, orderOf_rs hn])
    have hv2 := hsq ⟨ι (r n ^ (2 ^ (n - 3))), hvQ⟩ (by rw [orderOf_ambientHom, orderOf_sdV hn])
    obtain ⟨ψ, hψ⟩ := exists_mulAut_eq_or_eq_inv eQ _ _ hy2 hv2
    have hψmem : ψ ∈ Q.normalizerMonoidHom.range := by
      rw [htop]
      exact Subgroup.mem_top ψ
    obtain ⟨h, hh⟩ := hψmem
    have h1 := congrArg (fun φ : MulAut Q => ((φ ⟨ι (r n * s n), hyQ⟩ : Q) : H)) hh
    change (h : H) * ι (r n * s n) * (h : H)⁻¹ = ((ψ ⟨ι (r n * s n), hyQ⟩ : Q) : H) at h1
    have hvinv : IsConj (ι (r n ^ (2 ^ (n - 3)))) (ι (r n ^ (2 ^ (n - 3))))⁻¹ := by
      rw [← map_inv]
      exact ι.map_isConj (sdV_isConj_inv hn)
    rcases hψ with hψ | hψ
    · refine isConj_iff.mpr ⟨h, ?_⟩
      rw [h1, hψ]
    · have hc : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3))))⁻¹ := by
        refine isConj_iff.mpr ⟨h, ?_⟩
        rw [h1, hψ]
        rfl
      exact hc.trans hvinv.symm

theorem outerAutomizerIndex_qdQuaternion_eq_two (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S)
    (hb : ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) :
    outerAutomizerIndex (qdQuaternion (S : Subgroup H) f) = 2 := by
  by_contra h
  exact hb (isConj_of_outerAutomizerIndex_qdQuaternion_ne_two hn S f h)

end Automizers

section ClassCounts

variable [Finite H]

theorem involution_isConj_cases (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (x : H) (hx : orderOf x = 2) :
    IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (z n)) x ∨
      IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n)) x := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨y, hxy⟩ := InvolutionFusion.exists_ambient_conjugate_mem_sylow S x hp
  have hy := ambientHom_symm (S : Subgroup H) f y
  have ho : orderOf (f.symm y) = 2 := by
    rw [← orderOf_ambientHom (S : Subgroup H) f, hy, ← conjugate_orderOf_eq hxy, hx]
  rcases sd_involution_cases hn _ ho with h | h
  · left
    rw [← h, hy]
    exact hxy.symm
  · right
    have h' := (FocalFusion.ambientHom n (S : Subgroup H) f).map_isConj h
    rw [hy] at h'
    exact h'.trans hxy.symm

theorem orderFour_isConj_cases (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (x : H) (hx : orderOf x = 4) :
    IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3)))) x ∨
      IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n)) x := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨y, hxy⟩ := InvolutionFusion.exists_ambient_conjugate_mem_sylow S x hp
  have hy := ambientHom_symm (S : Subgroup H) f y
  have ho : orderOf (f.symm y) = 4 := by
    rw [← orderOf_ambientHom (S : Subgroup H) f, hy, ← conjugate_orderOf_eq hxy, hx]
  rcases sd_orderFour_cases hn _ ho with h | h
  · left
    have h' := (FocalFusion.ambientHom n (S : Subgroup H) f).map_isConj h
    rw [hy] at h'
    exact h'.trans hxy.symm
  · right
    have h' := (FocalFusion.ambientHom n (S : Subgroup H) f).map_isConj h
    rw [hy] at h'
    exact h'.trans hxy.symm

theorem involutionClassCount_eq_one (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (ha : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n))) :
    conjClassCountOfOrder H 2 = 1 :=
  conjClassCountOfOrder_eq_one _ _
    (by rw [orderOf_ambientHom, orderOf_z n (by omega)])
    (by rw [orderOf_ambientHom, orderOf_s n (by omega)])
    (involution_isConj_cases hn S f) ha.symm

theorem involutionClassCount_eq_two (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (ha : ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (z n))) :
    conjClassCountOfOrder H 2 = 2 :=
  conjClassCountOfOrder_eq_two _ _
    (by rw [orderOf_ambientHom, orderOf_z n (by omega)])
    (by rw [orderOf_ambientHom, orderOf_s n (by omega)])
    (involution_isConj_cases hn S f) (fun h => ha h.symm)

theorem orderFourClassCount_eq_one (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hb : IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) :
    conjClassCountOfOrder H 4 = 1 :=
  conjClassCountOfOrder_eq_one _ _
    (by rw [orderOf_ambientHom, orderOf_sdV hn])
    (by rw [orderOf_ambientHom, orderOf_rs hn])
    (orderFour_isConj_cases hn S f) hb.symm

theorem orderFourClassCount_eq_two (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hb : ¬ IsConj (FocalFusion.ambientHom n (S : Subgroup H) f (r n * s n))
      (FocalFusion.ambientHom n (S : Subgroup H) f (r n ^ (2 ^ (n - 3))))) :
    conjClassCountOfOrder H 4 = 2 :=
  conjClassCountOfOrder_eq_two _ _
    (by rw [orderOf_ambientHom, orderOf_sdV hn])
    (by rw [orderOf_ambientHom, orderOf_rs hn])
    (orderFour_isConj_cases hn S f) (fun h => hb h.symm)

end ClassCounts

end CFSG.QuasiDihedralFusion

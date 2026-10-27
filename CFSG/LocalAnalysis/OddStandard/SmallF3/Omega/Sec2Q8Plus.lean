module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketChain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketCentral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Q8Type
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeHigh

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem mul_self_eq_one_of_q8_lifts {G : Type} [Group G] {p q r : G}
    (hp : ∀ y, p * y = y * p) (hpp : p * p = 1)
    (hb : r * r = q * q ∨ r * r = p * (q * q))
    (hc : r * q = q⁻¹ * r ∨ r * q = p * (q⁻¹ * r)) : (q * q) * (q * q) = 1 := by
  obtain ⟨z1, hz1, hqr⟩ : ∃ z1 : G, (∀ y, z1 * y = y * z1) ∧ q * q = (r * r) * z1 := by
    rcases hb with h | h
    · exact ⟨1, fun y => by simp, by rw [mul_one, h]⟩
    · refine ⟨p, hp, ?_⟩
      calc q * q = (p * p) * (q * q) := by rw [hpp, one_mul]
        _ = p * (p * (q * q)) := mul_assoc _ _ _
        _ = p * ((q * q) * p) := by rw [hp (q * q)]
        _ = (p * (q * q)) * p := (mul_assoc _ _ _).symm
        _ = (r * r) * p := by rw [h]
  obtain ⟨z2, hz2, hz2sq, hrq⟩ :
      ∃ z2 : G, (∀ y, z2 * y = y * z2) ∧ z2 * z2 = 1 ∧ r * q * r⁻¹ = q⁻¹ * z2 := by
    rcases hc with h | h
    · exact ⟨1, fun y => by simp, mul_one 1, by rw [h]; group⟩
    · refine ⟨p, hp, hpp, ?_⟩
      calc r * q * r⁻¹ = p * (q⁻¹ * r) * r⁻¹ := by rw [h]
        _ = p * q⁻¹ := by group
        _ = q⁻¹ * p := hp q⁻¹
  have hconj : r * (q * q) * r⁻¹ = q * q := by
    calc r * (q * q) * r⁻¹
        = r * ((r * r) * z1) * r⁻¹ := by rw [← hqr]
      _ = (r * (r * r) * r⁻¹) * (r * z1 * r⁻¹) := by group
      _ = r * r * z1 := by
            rw [show r * (r * r) * r⁻¹ = r * r from by group,
                show r * z1 * r⁻¹ = z1 from by rw [← hz1 r]; group]
      _ = q * q := hqr.symm
  have hconj2 : r * (q * q) * r⁻¹ = (q * q)⁻¹ * (z2 * z2) := by
    have hsq : r * (q * q) * r⁻¹ = (q⁻¹ * z2) * (q⁻¹ * z2) := by
      calc r * (q * q) * r⁻¹
          = (r * q * r⁻¹) * (r * q * r⁻¹) := by group
        _ = (q⁻¹ * z2) * (q⁻¹ * z2) := by rw [hrq]
    rw [hsq]
    calc (q⁻¹ * z2) * (q⁻¹ * z2)
        = q⁻¹ * (z2 * q⁻¹) * z2 := by group
      _ = q⁻¹ * (q⁻¹ * z2) * z2 := by rw [hz2 q⁻¹]
      _ = (q * q)⁻¹ * (z2 * z2) := by group
  have hseq : q * q = (q * q)⁻¹ := by
    have h := hconj.symm.trans hconj2
    rw [hz2sq, mul_one] at h
    exact h
  exact (mul_eq_one_iff_eq_inv).mpr hseq

theorem q8_lift_relations (hQ : Q.Nondegenerate) {f : QuaternionGroup 2 →* omegaProj hQ}
    {q r : omegaGroup hQ} (hq : omegaToProj hQ q = f (QuaternionGroup.a 1))
    (hr : omegaToProj hQ r = f (QuaternionGroup.xa 0)) :
    omegaToProj hQ (q * q) = f (QuaternionGroup.a 2) ∧
      ((r : OGroup Q) * (r : OGroup Q) = (q : OGroup Q) * (q : OGroup Q) ∨
        (r : OGroup Q) * (r : OGroup Q) = piOrth Q * ((q : OGroup Q) * (q : OGroup Q))) ∧
      ((r : OGroup Q) * (q : OGroup Q) = (q : OGroup Q)⁻¹ * (r : OGroup Q) ∨
        (r : OGroup Q) * (q : OGroup Q) = piOrth Q * ((q : OGroup Q)⁻¹ * (r : OGroup Q))) := by
  have ha1sq : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide +kernel
  have hxa0sq : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by decide +kernel
  have hconjQ : (QuaternionGroup.a 1 : QuaternionGroup 2)⁻¹ * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide +kernel
  have hρqq : omegaToProj hQ (q * q) = f (QuaternionGroup.a 2) := by
    calc omegaToProj hQ (q * q) = f (QuaternionGroup.a 1) * f (QuaternionGroup.a 1) := by
          rw [map_mul, hq]
      _ = f (QuaternionGroup.a 1 * QuaternionGroup.a 1) := (map_mul f _ _).symm
      _ = f (QuaternionGroup.a 2) := by rw [ha1sq]
  have hρrr : omegaToProj hQ (r * r) = f (QuaternionGroup.a 2) := by
    calc omegaToProj hQ (r * r) = f (QuaternionGroup.xa 0) * f (QuaternionGroup.xa 0) := by
          rw [map_mul, hr]
      _ = f (QuaternionGroup.xa 0 * QuaternionGroup.xa 0) := (map_mul f _ _).symm
      _ = f (QuaternionGroup.a 2) := by rw [hxa0sq]
  have hρrq : omegaToProj hQ (r * q) = omegaToProj hQ (q⁻¹ * r) := by
    calc omegaToProj hQ (r * q) = f (QuaternionGroup.xa 0) * f (QuaternionGroup.a 1) := by
          rw [map_mul, hq, hr]
      _ = f (QuaternionGroup.xa 0 * QuaternionGroup.a 1) := (map_mul f _ _).symm
      _ = f ((QuaternionGroup.a 1)⁻¹ * QuaternionGroup.xa 0) := by rw [hconjQ]
      _ = (f (QuaternionGroup.a 1))⁻¹ * f (QuaternionGroup.xa 0) := by rw [map_mul, map_inv]
      _ = omegaToProj hQ (q⁻¹ * r) := by rw [map_mul, map_inv, hq, hr]
  exact ⟨hρqq, omegaToProj_eq_iff hQ (hρqq.trans hρrr.symm), omegaToProj_eq_iff hQ hρrq.symm⟩

theorem exists_pocket_chain_of_invType (hQ : Q.Nondegenerate) (z : omegaGroup hQ)
    (hs : (z : OGroup Q) * z = 1) (htype : invType (z : OGroup Q) = (4, 1))
    (hW : 0 < Module.finrank (ZMod 3) (fixSp (z : OGroup Q))) :
    ∃ K M : Subgroup (omegaGroup hQ), z ∈ K ∧ K ≤ M ∧
      M ≤ Subgroup.centralizer ({z} : Set (omegaGroup hQ)) ∧
      (∀ h ∈ K, ∀ l ∈ M, l * h * l⁻¹ ∈ K) ∧
      (∀ l ∈ M, ∀ c ∈ Subgroup.centralizer ({z} : Set (omegaGroup hQ)), c * l * c⁻¹ ∈ M) ∧
      IsSL23Mod K ∧ ∀ k ∈ K, (k : OGroup Q) ≠ piOrth Q := by
  have hdim4 : Module.finrank (ZMod 3) (commSp (z : OGroup Q)) = 4 := by
    simpa only [invType, invDim] using congrArg Prod.fst htype
  have hsgn : quadSign (Q.restrict (commSp (z : OGroup Q))) = 1 := by
    simpa only [invType, invSign] using congrArg Prod.snd htype
  obtain ⟨K₁, hπ, hK₁Ω, hK₁n, hK₁⟩ :=
    exists_pocket_plus4 (nondegenerate_restrict_commSp hQ hs) hdim4 hsgn
  exact exists_pocket_chain_of_block hQ z hs (by omega) hW hπ hK₁Ω hK₁n hK₁

theorem isI4PlusIn_top_of_quaternion_omegaProj (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) {f : QuaternionGroup 2 →* omegaProj hQ}
    (hf : Function.Injective f) :
    IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) (f (QuaternionGroup.a 2)) := by
  have ha2ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide +kernel
  have ha2 : f (QuaternionGroup.a 2) ≠ 1 := fun h => ha2ne (hf (by rw [h, map_one]))
  obtain ⟨q, hq⟩ := omegaToProj_surjective hQ (f (QuaternionGroup.a 1))
  obtain ⟨r, hr⟩ := omegaToProj_surjective hQ (f (QuaternionGroup.xa 0))
  obtain ⟨hρqq, hb, hc⟩ := q8_lift_relations hQ hq hr
  have hyy : ((q : OGroup Q) * (q : OGroup Q)) * ((q : OGroup Q) * (q : OGroup Q)) = 1 :=
    mul_self_eq_one_of_q8_lifts (G := OGroup Q) (p := piOrth Q) (q := (q : OGroup Q))
      (r := (r : OGroup Q)) (fun y => (mul_piOrth_comm y).symm) piOrth_mul_self hb hc
  have hy1 : (q : OGroup Q) * (q : OGroup Q) ≠ 1 := fun h =>
    ha2 (hρqq.symm.trans ((omegaToProj_eq_one_iff hQ (q * q)).mpr (Or.inl h)))
  have hyπ : (q : OGroup Q) * (q : OGroup Q) ≠ piOrth Q := fun h =>
    ha2 (hρqq.symm.trans ((omegaToProj_eq_one_iff hQ (q * q)).mpr (Or.inr h)))
  have htype : invType ((q : OGroup Q) * (q : OGroup Q)) = (4, 1) :=
    invType_eq_of_q8_lift hQ hdim q.2 r.2 hyy hy1 hyπ hb hc
  have hfix : 0 < Module.finrank (ZMod 3) (fixSp ((q : OGroup Q) * (q : OGroup Q))) := by
    have h1 := finrank_fixSp_add_finrank_commSp ((q : OGroup Q) * (q : OGroup Q))
    have h2 : Module.finrank (ZMod 3) (commSp ((q : OGroup Q) * (q : OGroup Q))) = 4 := by
      simpa only [invType, invDim] using congrArg Prod.fst htype
    omega
  obtain ⟨K, M, hzK, hKM, hMC, hKM', hMC', hKsl, hKπ⟩ :=
    exists_pocket_chain_of_invType hQ (q * q) hyy htype hfix
  have hzz : orderOf (q * q : omegaGroup hQ) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hyy)
      (fun h => hy1 (congrArg Subtype.val h))
  have hdis : Disjoint K (omegaToProj hQ).ker := by
    rw [Subgroup.disjoint_def]
    intro k hk hkρ
    rcases (omegaToProj_eq_one_iff hQ k).mp (MonoidHom.mem_ker.mp hkρ) with h | h
    · exact Subtype.ext h
    · exact absurd h (hKπ k hk)
  have h := isI4PlusIn_map_of_chain (omegaToProj hQ) (omegaToProj_surjective hQ)
    (fun m hm g => omegaToProj_ker_central hQ (MonoidHom.mem_ker.mp hm) g) hzz hzK hKM hMC hKM'
    hMC' hKsl hdis
  rwa [hρqq] at h

theorem asc82Omega8PlusPocket_holds : Asc82Omega8PlusPocket := by
  intro X _ hX f hf
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, -, ⟨e⟩⟩ := isOmegaStar_of_lieModel_plus hX
  letI := i1
  letI := i2
  letI := i3
  have hf' : Function.Injective (e.toMonoidHom.comp f) := e.injective.comp hf
  have h := isI4PlusIn_top_of_quaternion_omegaProj hQ hdim hf'
  have h2 := isI4PlusIn_top_map_mulEquiv e.symm h
  have hback : e.symm ((e.toMonoidHom.comp f) (QuaternionGroup.a 2)) =
      f (QuaternionGroup.a 2) := e.symm_apply_apply _
  rwa [hback] at h2

end CFSG.OddStandard.SmallF3.Omega

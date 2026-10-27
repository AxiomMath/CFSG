module

public import CFSG.CGT.PushingUpLit.T2KR.MMCoord

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization

variable {G : Type} [Group G] [Finite G]

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem conj_inv_mem (m : ↥M) {l : G} (hl : l ∈ L) : (m : G)⁻¹ * l * (m : G) ∈ L := by
  have := (Subgroup.mem_normalizer_iff.1 (H.normal (M.inv_mem m.2)) l).1 hl
  simpa using this

@[expose] noncomputable def cinv (m : ↥M) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    Matrix.SpecialLinearGroup (Fin 2) (Fq n) :=
  H.D.φ ⟨(m : G)⁻¹ * (H.D.sec g : G) * (m : G), H.conj_inv_mem m (H.D.sec g).2⟩

theorem slPerm_cinv (m : ↥M) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    slPerm (Fq n) (H.cinv m g) = (H.actHom m)⁻¹ * slPerm (Fq n) g * H.actHom m := by
  set l : ↥L := H.D.sec g with hl
  have hm' := H.conj_inv_mem m l.2
  show slPerm (Fq n) (H.D.φ ⟨(m : G)⁻¹ * (l : G) * (m : G), hm'⟩) = _
  rw [← H.actHom_L ⟨(m : G)⁻¹ * (l : G) * (m : G), hm'⟩]
  have e1 : (⟨(m : G)⁻¹ * (l : G) * (m : G), H.le hm'⟩ : ↥M) =
      m⁻¹ * ⟨(l : G), H.le l.2⟩ * m := Subtype.ext (by simp)
  have e2 : slPerm (Fq n) g = H.actHom ⟨(l : G), H.le l.2⟩ := by
    rw [H.actHom_L, hl, H.D.φ_sec]
  rw [e2, e1, map_mul, map_mul, map_inv]

theorem actHom_cinv (m : ↥M) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) (w : Fin 2 → Fq n) :
    H.actHom m (H.cinv m g • w) = g • H.actHom m w := by
  have h1 : H.actHom m * slPerm (Fq n) (H.cinv m g) = slPerm (Fq n) g * H.actHom m := by
    rw [H.slPerm_cinv]
    group
  exact congrArg (fun p : Equiv.Perm (Fin 2 → Fq n) => p w) h1

theorem cinv_mul (m : ↥M) (g g' : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    H.cinv m (g * g') = H.cinv m g * H.cinv m g' := by
  apply slPerm_injective
  rw [map_mul, H.slPerm_cinv, H.slPerm_cinv, H.slPerm_cinv, map_mul]
  group

@[expose] noncomputable def Tm (m : ↥M) (f : Matrix.SpecialLinearGroup (Fin 2) (Fq n) → Fin 2 → Fq n) :
    Matrix.SpecialLinearGroup (Fin 2) (Fq n) → Fin 2 → Fq n :=
  fun g => H.actHom m (f (H.cinv m g))

theorem Tm_add (m : ↥M) (f f' : Matrix.SpecialLinearGroup (Fin 2) (Fq n) → Fin 2 → Fq n) :
    H.Tm m (f + f') = H.Tm m f + H.Tm m f' := by
  funext g
  exact H.actHom_add m _ _

theorem Tm_smul (m : ↥M) (B : Fq n)
    (f : Matrix.SpecialLinearGroup (Fin 2) (Fq n) → Fin 2 → Fq n) :
    H.Tm m (B • f) = H.chi m B • H.Tm m f := by
  funext g
  exact H.isSemilinear_chi m B (f (H.cinv m g))

theorem Tm_mem_Z1A (m : ↥M) {f : Matrix.SpecialLinearGroup (Fin 2) (Fq n) → Fin 2 → Fq n}
    (hf : f ∈ Z1A (mu2 (F := Fq n))) : H.Tm m f ∈ Z1A (mu2 (F := Fq n)) := by
  intro g g'
  show H.actHom m (f (H.cinv m (g * g'))) = H.actHom m (f (H.cinv m g)) +
    mu2 g (H.actHom m (f (H.cinv m g')))
  rw [H.cinv_mul, hf, H.actHom_add, mu2_apply]
  congr 1
  exact H.actHom_cinv m g _

theorem Tm_cob (m : ↥M) (w : Fin 2 → Fq n) :
    H.Tm m (coboundaryA (mu2 (F := Fq n)) w) = coboundaryA (mu2 (F := Fq n)) (H.actHom m w) := by
  funext g
  show H.actHom m (mu2 (H.cinv m g) w - w) = mu2 g (H.actHom m w) - H.actHom m w
  have h1 : H.actHom m (mu2 (H.cinv m g) w) = mu2 g (H.actHom m w) := H.actHom_cinv m g w
  have h2 : H.actHom m (mu2 (H.cinv m g) w - w) = H.actHom m (mu2 (H.cinv m g) w) - H.actHom m w := by
    have := H.actHom_add m (mu2 (H.cinv m g) w - w) w
    rw [sub_add_cancel] at this
    rw [this]
    abel
  rw [h2, h1]

theorem cob_smul (B : Fq n) (w : Fin 2 → Fq n) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    coboundaryA (mu2 (F := Fq n)) (B • w) g = B • coboundaryA (mu2 (F := Fq n)) w g := by
  simp only [coboundaryA_apply, mu2_apply, Matrix.mulVec_smul, smul_sub]

theorem cob_add (w w' : Fin 2 → Fq n) :
    coboundaryA (mu2 (F := Fq n)) (w + w') =
      coboundaryA (mu2 (F := Fq n)) w + coboundaryA (mu2 (F := Fq n)) w' := map_add _ _ _

include H in
theorem kap_conj (m : ↥M) {u : G} (hu : u ∈ QM L M)
    (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    kap H.D ((m : G) * u * (m : G)⁻¹) g = H.Tm m (kap H.D u) g := by
  rw [kappa_def]
  set l : ↥L := H.D.sec g with hl
  have e : delta ((m : G) * u * (m : G)⁻¹) (l : G) =
      (m : G) * delta u ((m : G)⁻¹ * (l : G) * (m : G)) * (m : G)⁻¹ := by
    simp only [delta]
    group
  have hl' := H.conj_inv_mem m l.2
  have hV : delta u ((m : G)⁻¹ * (l : G) * (m : G)) ∈ blockU L :=
    H.nat.delta_mem H.normal hu hl'
  rw [e, ← H.act_vec (m : G) hV]
  show H.act m _ = H.actHom m (kap H.D u (H.cinv m g))
  have h2 : kap H.D u (H.cinv m g) = H.D.ψe (delta u ((m : G)⁻¹ * (l : G) * (m : G))) :=
    kappa_apply H.nat H.D H.le H.normal hu hl'
  rw [h2]
  rfl

include H in
theorem exists_Tm_f0 (m : ↥M) : ∃ (c : Fq n) (w₀ : Fin 2 → Fq n), ∀ g,
    H.Tm m f0 g = coboundaryA (mu2 (F := Fq n)) w₀ g + c • f0 g := by
  obtain ⟨c, hc⟩ := exists_sub_mem_B1A (a := n) H.hcard (by have := H.nat.two_le; omega)
    (H.Tm_mem_Z1A m f0_mem)
  obtain ⟨w₀, hw₀⟩ := hc
  refine ⟨c, w₀, fun g => ?_⟩
  have := congrFun hw₀ g
  simp only [Pi.sub_apply, Pi.smul_apply] at this
  rw [this]
  abel

@[expose] noncomputable def cc (m : ↥M) : Fq n := Classical.choose (H.exists_Tm_f0 m)

@[expose] noncomputable def ww (m : ↥M) : Fin 2 → Fq n :=
  Classical.choose (Classical.choose_spec (H.exists_Tm_f0 m))

theorem Tm_f0 (m : ↥M) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    H.Tm m f0 g = coboundaryA (mu2 (F := Fq n)) (H.ww m) g + H.cc m • f0 g :=
  Classical.choose_spec (Classical.choose_spec (H.exists_Tm_f0 m)) g

include H in
theorem theta_conj (m : ↥M) (u : ↥(QM L M)) (hmu : (m : G) * u * (m : G)⁻¹ ∈ QM L M) :
    H.theta ⟨(m : G) * u * (m : G)⁻¹, hmu⟩ = H.cc m * H.chi m (H.theta u) := by
  have key : ∀ g, coboundaryA (mu2 (F := Fq n)) (H.vco ⟨(m : G) * u * (m : G)⁻¹, hmu⟩) g +
        H.theta ⟨(m : G) * u * (m : G)⁻¹, hmu⟩ • f0 g =
      coboundaryA (mu2 (F := Fq n)) (H.actHom m (H.vco u) + H.chi m (H.theta u) • H.ww m) g +
        (H.cc m * H.chi m (H.theta u)) • f0 g := by
    intro g
    rw [← H.kap_eq, H.kap_conj m u.2 g]
    have hk : kap H.D (u : G) =
        coboundaryA (mu2 (F := Fq n)) (H.vco u) + H.theta u • f0 := funext (H.kap_eq u)
    rw [hk, H.Tm_add, H.Tm_cob, H.Tm_smul]
    show _ + (H.chi m (H.theta u) • H.Tm m f0) g = _
    rw [Pi.smul_apply, H.Tm_f0, cob_add, Pi.add_apply, cob_smul]
    module
  exact (H.decomp_unique key).2

theorem cinv_cinv {m : ↥M} (hm : m * m = 1) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    H.cinv m (H.cinv m g) = g := by
  apply slPerm_injective
  have h1 : H.actHom m * H.actHom m = 1 := by rw [← map_mul, hm, map_one]
  have h2 : (H.actHom m)⁻¹ = H.actHom m := inv_eq_of_mul_eq_one_right h1
  rw [H.slPerm_cinv, H.slPerm_cinv, h2]
  calc H.actHom m * (H.actHom m * slPerm (Fq n) g * H.actHom m) * H.actHom m =
      (H.actHom m * H.actHom m) * slPerm (Fq n) g * (H.actHom m * H.actHom m) := by group
    _ = slPerm (Fq n) g := by rw [h1]; group

theorem Tm_Tm {m : ↥M} (hm : m * m = 1)
    (f : Matrix.SpecialLinearGroup (Fin 2) (Fq n) → Fin 2 → Fq n) : H.Tm m (H.Tm m f) = f := by
  funext g
  have h1 : H.actHom m * H.actHom m = 1 := by rw [← map_mul, hm, map_one]
  show H.actHom m (H.actHom m (f (H.cinv m (H.cinv m g)))) = f g
  rw [H.cinv_cinv hm]
  exact congrArg (fun p : Equiv.Perm (Fin 2 → Fq n) => p (f g)) h1

include H in
theorem cc_involution {m : ↥M} (hm : m * m = 1) : H.cc m * H.chi m (H.cc m) = 1 := by
  have e : H.Tm m f0 = coboundaryA (mu2 (F := Fq n)) (H.ww m) + H.cc m • f0 := funext (H.Tm_f0 m)
  have h2 : H.Tm m (H.Tm m f0) = f0 := H.Tm_Tm hm f0
  rw [e, H.Tm_add, H.Tm_cob, H.Tm_smul, e] at h2
  have h1 : (1 - H.chi m (H.cc m) * H.cc m) • (f0 : Matrix.SpecialLinearGroup (Fin 2) (Fq n) →
      Fin 2 → Fq n) ∈ B1A (mu2 (F := Fq n)) := by
    refine ⟨H.actHom m (H.ww m) + H.chi m (H.cc m) • H.ww m, ?_⟩
    funext g
    have := congrFun h2 g
    simp only [Pi.add_apply, Pi.smul_apply] at this
    rw [cob_add, Pi.add_apply, cob_smul, Pi.smul_apply]
    linear_combination (norm := module) this
  have := eq_zero_of_smul_f0_mem_B1A H.two_lt_card h1
  linear_combination -this

end MData

end CFSG.CGT.PushingUpLit.T2KR

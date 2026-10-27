module

public import CFSG.LargeExtraspecial.S3Qa
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.OrthoF2Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace S63

variable {G : Type} [Group G]

@[expose] def WeakCl (S : Setting G) : Prop :=
  ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z

variable {S : Setting G}

theorem WeakCl.eq_of_mem_Qa (hW : WeakCl S) {g k : G} (h : k * S.z * k⁻¹ ∈ S.Qa g) :
    k * S.z * k⁻¹ = g * S.z * g⁻¹ := by
  rw [S.Qa_eq_map] at h
  obtain ⟨u, hu, hku⟩ := h
  change g * u * g⁻¹ = k * S.z * k⁻¹ at hku
  have e : (g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹ = u := by
    calc (g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * S.z * k⁻¹) * g := by group
      _ = u := by rw [← hku]; group
  have h1 := hW (g⁻¹ * k) (e ▸ hu)
  calc k * S.z * k⁻¹ = g * ((g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹) * g⁻¹ := by group
    _ = g * S.z * g⁻¹ := by rw [h1]

theorem WeakCl.conjBy (hW : WeakCl S) (g : G) : WeakCl (S.conjBy g) := by
  intro k hk
  change k * (g * S.z * g⁻¹) * k⁻¹ ∈ S.Qa g at hk
  change k * (g * S.z * g⁻¹) * k⁻¹ = g * S.z * g⁻¹
  have e : k * (g * S.z * g⁻¹) * k⁻¹ = (k * g) * S.z * (k * g)⁻¹ := by group
  rw [e] at hk ⊢
  exact hW.eq_of_mem_Qa hk

theorem mem_Qa_mul_iff {c g y : G} : y ∈ S.Qa (c * g) ↔ c⁻¹ * y * c ∈ S.Qa g := by
  rw [S.Qa_eq_map, S.Qa_eq_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    change g * u * g⁻¹ = c⁻¹ * ((c * g) * u * (c * g)⁻¹) * c
    group
  · rintro ⟨u, hu, hcu⟩
    refine ⟨u, hu, ?_⟩
    change g * u * g⁻¹ = c⁻¹ * y * c at hcu
    change (c * g) * u * (c * g)⁻¹ = y
    calc (c * g) * u * (c * g)⁻¹ = c * (g * u * g⁻¹) * c⁻¹ := by group
      _ = y := by rw [hcu]; group

theorem conj_eq_of_commutator {m w a : G} (h : m * w * m⁻¹ * w⁻¹ = a) (ha : a * a = 1) :
    w * m * w⁻¹ = a * m := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  calc w * m * w⁻¹ = (m * w * m⁻¹ * w⁻¹)⁻¹ * m := by group
    _ = a * m := by rw [h, ha']

variable (S) in
structure Pair where
  g : G
  t : G
  hW : WeakCl S
  hxM : g * S.z * g⁻¹ ∈ S.M
  hxz : g * S.z * g⁻¹ ≠ S.z
  htQ : t ∈ S.QG
  hta : t ∈ S.Qa g
  ht1 : t ≠ 1

namespace Pair

variable (P : Pair S)

@[expose] def x : G := P.g * S.z * P.g⁻¹

theorem x_def : P.x = P.g * S.z * P.g⁻¹ := rfl

theorem x_mem_M : P.x ∈ S.M := P.hxM

theorem x_ne_z : P.x ≠ S.z := P.hxz

theorem x_mul_x : P.x * P.x = 1 := by
  calc P.x * P.x = P.g * (S.z * S.z) * P.g⁻¹ := by rw [x_def]; group
    _ = 1 := by rw [S.z_mul_z]; group

theorem x_inv : P.x⁻¹ = P.x := inv_eq_of_mul_eq_one_right P.x_mul_x

theorem x_comm_z : P.x * S.z = S.z * P.x := S.mem_M_iff.mp P.hxM

theorem x_not_mem_QG : P.x ∉ S.QG := fun h => P.hxz (P.hW _ h)

theorem x_mem_Qa : P.x ∈ S.Qa P.g := (S.conjBy P.g).z_mem_QG

theorem z_not_mem_Qa : S.z ∉ S.Qa P.g := fun h => P.hxz (by
  have h1 := P.hW.eq_of_mem_Qa (k := 1) (g := P.g) (by simpa using h)
  simpa using h1.symm)

theorem eq_x_of_mem_Qa {k : G} (h : k * S.z * k⁻¹ ∈ S.Qa P.g) : k * S.z * k⁻¹ = P.x :=
  P.hW.eq_of_mem_Qa h

theorem comm_x_of_mem_Qa {a : G} (ha : a ∈ S.Qa P.g) : a * P.x = P.x * a :=
  (S.conjBy P.g).z_comm_QG ha

theorem t_comm_x : P.t * P.x = P.x * P.t := P.comm_x_of_mem_Qa P.hta

theorem t_comm_z : P.t * S.z = S.z * P.t := S.z_comm_QG P.htQ

theorem t_ne_z : P.t ≠ S.z := fun h => P.z_not_mem_Qa (h ▸ P.hta)

theorem conj_ne_t_mul_x (k : G) : k * P.x * k⁻¹ ≠ P.t * P.x := by
  intro h
  have hmem : (k * P.g) * S.z * (k * P.g)⁻¹ ∈ S.Qa P.g := by
    have e : (k * P.g) * S.z * (k * P.g)⁻¹ = P.t * P.x := by rw [← h, x_def]; group
    rw [e]
    exact (S.Qa P.g).mul_mem P.hta P.x_mem_Qa
  have h1 := P.eq_x_of_mem_Qa hmem
  have e : (k * P.g) * S.z * (k * P.g)⁻¹ = P.t * P.x := by rw [← h, x_def]; group
  rw [e] at h1
  exact P.ht1 (mul_eq_right.mp h1)

theorem comm_t_of_comm_x {e : G} (he : e ∈ S.QG) (hex : e * P.x = P.x * e) :
    e * P.t = P.t * e := by
  have heM : e ∈ (S.conjBy P.g).M := mem_centralizer_singleton_iff.mpr hex
  have h1 : e * P.t * e⁻¹ * P.t⁻¹ ∈ S.Qa P.g :=
    (S.Qa P.g).mul_mem ((S.conjBy P.g).conj_mem_QG heM P.hta) ((S.Qa P.g).inv_mem P.hta)
  rcases S.commutator_eq_one_or_z he P.htQ with h | h
  · calc e * P.t = e * P.t * e⁻¹ * P.t⁻¹ * (P.t * e) := by group
      _ = P.t * e := by rw [h, one_mul]
  · exact absurd (h ▸ h1) P.z_not_mem_Qa

theorem conj_commutator_eq_inv (c : G) :
    P.x * (P.x * c * P.x⁻¹ * c⁻¹) * P.x⁻¹ = (P.x * c * P.x⁻¹ * c⁻¹)⁻¹ := by
  calc P.x * (P.x * c * P.x⁻¹ * c⁻¹) * P.x⁻¹ = (P.x * P.x) * c * P.x⁻¹ * c⁻¹ * P.x⁻¹ := by
        group
    _ = c * P.x * c⁻¹ * P.x⁻¹ := by rw [P.x_mul_x, P.x_inv]; group
    _ = (P.x * c * P.x⁻¹ * c⁻¹)⁻¹ := by group

theorem conj_eq_inv_commutator_mul (c : G) :
    c * P.x * c⁻¹ = (P.x * c * P.x⁻¹ * c⁻¹)⁻¹ * P.x := by
  group

end Pair

variable [Finite G]

variable (S) in
noncomputable abbrev rhoG {m : G} (hm : m ∈ S.M) : S.Qt ≃ₗ[ZMod 2] S.Qt :=
  ((S.ρ ⟨m, hm⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)

theorem rhoG_cl {m : G} (hm : m ∈ S.M) {w : G} (hw : w ∈ S.QG) :
    rhoG S hm (S.cl w) = S.cl (m * w * m⁻¹) :=
  S.ρ_cl ⟨m, hm⟩ hw

theorem rhoG_mem {m : G} (hm : m ∈ S.M) :
    rhoG S hm ∈ TauCeti.QuadraticMap.orthogonalGroup S.q :=
  (S.ρ ⟨m, hm⟩).2

theorem cl_commutator {m : G} (hm : m ∈ S.M) {w : G} (hw : w ∈ S.QG) :
    S.cl (m * w * m⁻¹ * w⁻¹) = rhoG S hm (S.cl w) - S.cl w := by
  rw [S.cl_mul (S.conj_mem_QG hm hw) (S.QG.inv_mem hw), S.cl_inv hw, rhoG_cl hm hw,
    sub_eq_add_neg, ZModModule.neg_eq_self]

theorem rhoG_cl_eq_iff {m : G} (hm : m ∈ S.M) {e : G} (he : e ∈ S.QG) :
    rhoG S hm (S.cl e) = S.cl e ↔ m * e * m⁻¹ = e ∨ m * e * m⁻¹ = e * S.z := by
  rw [rhoG_cl hm he, eq_comm, S.cl_eq_cl_iff he (S.conj_mem_QG hm he)]

theorem mem_commSpace_of_forall {m : G} (hm : m ∈ S.M) {v : S.Qt}
    (h : ∀ e ∈ S.QG, rhoG S hm (S.cl e) = S.cl e → polar S.q (S.cl e) v = 0) :
    v ∈ commSpace (rhoG S hm) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  rw [commSpace_eq_orthogonal_fixSpace_of_mem S.q_nondegenerate (rhoG_mem hm),
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  obtain ⟨e, he, rfl⟩ := S.exists_cl u
  change S.q.polarBilin (S.cl e) v = 0
  rw [polarBilin_apply_apply]
  exact h e he (mem_fixSpace.mp hu)

theorem exists_of_mem_commSpace {m : G} (hm : m ∈ S.M) {v : S.Qt}
    (hv : v ∈ commSpace (rhoG S hm)) : ∃ w ∈ S.QG, S.cl (m * w * m⁻¹ * w⁻¹) = v := by
  obtain ⟨u, hu⟩ := mem_commSpace.mp hv
  obtain ⟨w, hw, rfl⟩ := S.exists_cl u
  exact ⟨w, hw, by rw [cl_commutator hm hw, hu]⟩

namespace Pair

variable (P : Pair S)

theorem t_sq : P.t ^ 2 = 1 := S.QG_inf_Qa_sq P.hxz ⟨P.htQ, P.hta⟩

theorem t_mul_t : P.t * P.t = 1 := by rw [← pow_two]; exact P.t_sq

theorem tz_mul_tz : (P.t * S.z) * (P.t * S.z) = 1 := by
  calc (P.t * S.z) * (P.t * S.z) = P.t * (S.z * P.t) * S.z := by group
    _ = P.t * (P.t * S.z) * S.z := by rw [P.t_comm_z]
    _ = (P.t * P.t) * (S.z * S.z) := by group
    _ = 1 := by rw [P.t_mul_t, S.z_mul_z, one_mul]

omit [Finite G] in
theorem commutator_mem_QG {c : G} (hc : c ∈ S.QG) : P.x * c * P.x⁻¹ * c⁻¹ ∈ S.QG :=
  S.QG.mul_mem (S.conj_mem_QG P.x_mem_M hc) (S.QG.inv_mem hc)

theorem sq_commutator_eq_one {c : G} (hc : c ∈ S.QG) : (P.x * c * P.x⁻¹ * c⁻¹) ^ 2 = 1 := by
  by_contra hd
  obtain ⟨d, hd_def⟩ : ∃ d, P.x * c * P.x⁻¹ * c⁻¹ = d := ⟨_, rfl⟩
  rw [hd_def] at hd
  have hxM : P.x ∈ S.M := P.x_mem_M
  have hdQ : d ∈ S.QG := hd_def ▸ P.commutator_mem_QG hc
  have hd2 : d ^ 2 = S.z := (S.sq_eq_one_or_z hdQ).resolve_left hd
  have hdd : d * d = S.z := by rw [← pow_two]; exact hd2
  have hxd : P.x * d * P.x⁻¹ = d⁻¹ := by rw [← hd_def]; exact P.conj_commutator_eq_inv c
  have hdinv : d⁻¹ = d * S.z := by
    calc d⁻¹ = d⁻¹ * (d * d) * S.z := by rw [hdd, mul_assoc, S.z_mul_z, mul_one]
      _ = d * S.z := by group
  have hdx : d * P.x * d⁻¹ = S.z * P.x := by
    calc d * P.x * d⁻¹ = d * (P.x * d * P.x⁻¹)⁻¹ * P.x := by group
      _ = d * d * P.x := by rw [hxd, inv_inv]
      _ = S.z * P.x := by rw [hdd]
  have hρt : rhoG S hxM (S.cl P.t) = S.cl P.t := by
    rw [rhoG_cl hxM P.htQ]
    congr 1
    calc P.x * P.t * P.x⁻¹ = P.t * P.x * P.x⁻¹ := by rw [P.t_comm_x]
      _ = P.t := by group
  have hdt : d * P.t = P.t * d := by
    rw [← S.polar_cl_eq_zero_iff hdQ P.htQ, ← hd_def, cl_commutator hxM hc,
      QuadraticMap.polar_sub_left]
    have h1 : polar S.q (rhoG S hxM (S.cl c)) (S.cl P.t) = polar S.q (S.cl c) (S.cl P.t) := by
      conv_lhs => rw [← hρt]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (rhoG_mem hxM) _ _
    rw [h1, sub_self]
  have hfix : ∀ e ∈ S.QG, rhoG S hxM (S.cl e) = S.cl e → polar S.q (S.cl e) (S.cl P.t) = 0 := by
    intro e he hfe
    rw [S.polar_cl_eq_zero_iff he P.htQ]
    rcases (rhoG_cl_eq_iff hxM he).mp hfe with h | h
    · refine P.comm_t_of_comm_x he ?_
      calc e * P.x = (P.x * e * P.x⁻¹) * P.x := by rw [h]
        _ = P.x * e := by group
    · have hedQ : e * d ∈ S.QG := S.QG.mul_mem he hdQ
      have hzd : d * S.z = S.z * d := S.z_comm_QG hdQ
      have h1 : P.x * (e * d) * P.x⁻¹ = e * d := by
        calc P.x * (e * d) * P.x⁻¹ = (P.x * e * P.x⁻¹) * (P.x * d * P.x⁻¹) := by group
          _ = e * S.z * (d * S.z) := by rw [h, hxd, hdinv]
          _ = e * (S.z * d) * S.z := by group
          _ = e * (d * S.z) * S.z := by rw [hzd]
          _ = e * d * (S.z * S.z) := by group
          _ = e * d := by rw [S.z_mul_z, mul_one]
      have h2 : (e * d) * P.x = P.x * (e * d) := by
        calc (e * d) * P.x = (P.x * (e * d) * P.x⁻¹) * P.x := by rw [h1]
          _ = P.x * (e * d) := by group
      have h3 := P.comm_t_of_comm_x hedQ h2
      calc e * P.t = e * (d * P.t) * d⁻¹ := by rw [hdt]; group
        _ = (e * d) * P.t * d⁻¹ := by group
        _ = P.t * (e * d) * d⁻¹ := by rw [h3]
        _ = P.t * e := by group
  obtain ⟨w, hw, hcl⟩ := exists_of_mem_commSpace hxM (mem_commSpace_of_forall hxM hfix)
  have hwQ : P.x * w * P.x⁻¹ * w⁻¹ ∈ S.QG := P.commutator_mem_QG hw
  rcases (S.cl_eq_cl_iff P.htQ hwQ).mp hcl.symm with h | h
  · exact P.conj_ne_t_mul_x w (conj_eq_of_commutator h P.t_mul_t)
  · have h1 := conj_eq_of_commutator h P.tz_mul_tz
    apply P.conj_ne_t_mul_x (w * d)
    calc w * d * P.x * (w * d)⁻¹ = w * (d * P.x * d⁻¹) * w⁻¹ := by group
      _ = (w * S.z * w⁻¹) * (w * P.x * w⁻¹) := by rw [hdx]; group
      _ = S.z * (P.t * S.z * P.x) := by rw [S.z_comm_QG hw, h1]; group
      _ = (S.z * P.t) * S.z * P.x := by group
      _ = (P.t * S.z) * S.z * P.x := by rw [P.t_comm_z]
      _ = P.t * (S.z * S.z) * P.x := by group
      _ = P.t * P.x := by rw [S.z_mul_z, mul_one]

theorem conj_eq_commutator_mul {c : G} (hc : c ∈ S.QG) :
    c * P.x * c⁻¹ = (P.x * c * P.x⁻¹ * c⁻¹) * P.x := by
  have h2 := P.sq_commutator_eq_one hc
  rw [pow_two] at h2
  rw [P.conj_eq_inv_commutator_mul c, inv_eq_of_mul_eq_one_right h2]

theorem commutator_mem {c : G} (hc : c ∈ S.QG) (hct : c * P.t = P.t * c) :
    P.x * c * P.x⁻¹ * c⁻¹ = 1 ∨ P.x * c * P.x⁻¹ * c⁻¹ = P.t ∨
      P.x * c * P.x⁻¹ * c⁻¹ = S.z ∨ P.x * c * P.x⁻¹ * c⁻¹ = P.t * S.z := by
  by_contra hne
  push Not at hne
  obtain ⟨hd1, hdt, hdz, hdtz⟩ := hne
  obtain ⟨d, hd_def⟩ : ∃ d, P.x * c * P.x⁻¹ * c⁻¹ = d := ⟨_, rfl⟩
  rw [hd_def] at hd1 hdt hdz hdtz
  have hxM : P.x ∈ S.M := P.x_mem_M
  have hdQ : d ∈ S.QG := hd_def ▸ P.commutator_mem_QG hc
  have hd2 : d * d = 1 := by rw [← pow_two, ← hd_def]; exact P.sq_commutator_eq_one hc
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hxd : P.x * d = d * P.x := by
    have h := P.conj_commutator_eq_inv c
    rw [hd_def, hdi] at h
    calc P.x * d = (P.x * d * P.x⁻¹) * P.x := by group
      _ = d * P.x := by rw [h]
  have hxdx : P.x * (d * P.x) = d := by rw [← mul_assoc, hxd, mul_assoc, P.x_mul_x, mul_one]
  have hy : (c * P.g) * S.z * (c * P.g)⁻¹ = d * P.x := by
    calc (c * P.g) * S.z * (c * P.g)⁻¹ = c * P.x * c⁻¹ := by rw [x_def]; group
      _ = d * P.x := by rw [P.conj_eq_commutator_mul hc, hd_def]
  have hyx : (d * P.x) * P.x = P.x * (d * P.x) := by
    rw [hxdx, mul_assoc, P.x_mul_x, mul_one]
  have hyM : d * P.x ∈ (S.conjBy P.g).M := mem_centralizer_singleton_iff.mpr hyx
  have hty : P.t ∈ S.Qa (c * P.g) := by
    rw [mem_Qa_mul_iff]
    have : c⁻¹ * P.t * c = P.t := by rw [mul_assoc, ← hct]; group
    rw [this]
    exact P.hta
  have hyQ : d * P.x ∉ S.QG := fun h => P.x_not_mem_QG (by
    have := S.QG.mul_mem (S.QG.inv_mem hdQ) h
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
  have hxQy : P.x ∉ S.Qa (c * P.g) := by
    intro h
    have h1 := P.hW.eq_of_mem_Qa (g := c * P.g) (k := P.g) h
    rw [hy, ← x_def] at h1
    exact hd1 (by simpa using h1.symm)
  have ha : ∀ e ∈ S.Qa P.g, e * (d * P.x) = (d * P.x) * e → e * P.t = P.t * e := by
    intro e he hey
    have heM : e ∈ (S.conjBy (c * P.g)).M := by
      refine mem_centralizer_singleton_iff.mpr ?_
      change e * ((c * P.g) * S.z * (c * P.g)⁻¹) = ((c * P.g) * S.z * (c * P.g)⁻¹) * e
      rw [hy]
      exact hey
    have h1 : e * P.t * e⁻¹ * P.t⁻¹ ∈ S.Qa (c * P.g) :=
      (S.Qa (c * P.g)).mul_mem ((S.conjBy (c * P.g)).conj_mem_QG heM hty)
        ((S.Qa (c * P.g)).inv_mem hty)
    rcases (S.conjBy P.g).commutator_eq_one_or_z he P.hta with h | h
    · calc e * P.t = e * P.t * e⁻¹ * P.t⁻¹ * (P.t * e) := by group
        _ = P.t * e := by rw [h, one_mul]
    · change e * P.t * e⁻¹ * P.t⁻¹ = P.x at h
      exact absurd (h ▸ h1) hxQy
  have hfix : ∀ e ∈ (S.conjBy P.g).QG,
      rhoG (S.conjBy P.g) hyM ((S.conjBy P.g).cl e) = (S.conjBy P.g).cl e →
        polar (S.conjBy P.g).q ((S.conjBy P.g).cl e) ((S.conjBy P.g).cl P.t) = 0 := by
    intro e he hfe
    rw [(S.conjBy P.g).polar_cl_eq_zero_iff he P.hta]
    rcases (rhoG_cl_eq_iff hyM he).mp hfe with h | h
    · refine ha e he ?_
      calc e * (d * P.x) = (d * P.x * e * (d * P.x)⁻¹) * (d * P.x) := by rw [h]
        _ = (d * P.x) * e := by group
    · exfalso
      change d * P.x * e * (d * P.x)⁻¹ = e * P.x at h
      apply hdz
      have h1 : (e⁻¹ * (c * P.g)) * S.z * (e⁻¹ * (c * P.g))⁻¹ = d := by
        calc (e⁻¹ * (c * P.g)) * S.z * (e⁻¹ * (c * P.g))⁻¹
            = e⁻¹ * ((c * P.g) * S.z * (c * P.g)⁻¹) * e := by group
          _ = e⁻¹ * ((d * P.x) * e * (d * P.x)⁻¹) * (d * P.x) := by rw [hy]; group
          _ = P.x * (d * P.x) := by rw [h]; group
          _ = d := hxdx
      rw [← h1]
      exact P.hW _ (h1 ▸ hdQ)
  obtain ⟨w, hw, hcl⟩ := exists_of_mem_commSpace hyM (mem_commSpace_of_forall hyM hfix)
  have hwQ : d * P.x * w * (d * P.x)⁻¹ * w⁻¹ ∈ (S.conjBy P.g).QG :=
    (S.conjBy P.g).QG.mul_mem ((S.conjBy P.g).conj_mem_QG hyM hw)
      ((S.conjBy P.g).QG.inv_mem hw)
  have htx : (P.t * P.x) * (P.t * P.x) = 1 := by
    calc (P.t * P.x) * (P.t * P.x) = P.t * (P.x * P.t) * P.x := by group
      _ = P.t * (P.t * P.x) * P.x := by rw [P.t_comm_x]
      _ = (P.t * P.t) * (P.x * P.x) := by group
      _ = 1 := by rw [P.t_mul_t, P.x_mul_x, one_mul]
  have hwy : w * (d * P.x) * w⁻¹ = P.t * (d * P.x) := by
    rcases ((S.conjBy P.g).cl_eq_cl_iff P.hta hwQ).mp hcl.symm with h | h
    · exact conj_eq_of_commutator h P.t_mul_t
    · exfalso
      have h1 := conj_eq_of_commutator h htx
      change w * (d * P.x) * w⁻¹ = P.t * P.x * (d * P.x) at h1
      apply hdtz
      have h2 : (w * (c * P.g)) * S.z * (w * (c * P.g))⁻¹ = P.t * d := by
        calc (w * (c * P.g)) * S.z * (w * (c * P.g))⁻¹
            = w * ((c * P.g) * S.z * (c * P.g)⁻¹) * w⁻¹ := by group
          _ = P.t * (P.x * (d * P.x)) := by rw [hy, h1]; group
          _ = P.t * d := by rw [hxdx]
      have h3 := P.hW _ (h2 ▸ S.QG.mul_mem P.htQ hdQ)
      rw [h2] at h3
      calc d = P.t⁻¹ * (P.t * d) := by group
        _ = P.t * S.z := by rw [h3, inv_eq_of_mul_eq_one_right P.t_mul_t]
  have hty1 : P.t ≠ (S.conjBy (c * P.g)).z := by
    change P.t ≠ (c * P.g) * S.z * (c * P.g)⁻¹
    rw [hy]
    exact fun h => hyQ (h ▸ P.htQ)
  obtain ⟨f, hf, hft⟩ := (S.conjBy (c * P.g)).exists_conj_eq_mul_z hty P.ht1 hty1
  change f * P.t * f⁻¹ = P.t * ((c * P.g) * S.z * (c * P.g)⁻¹) at hft
  rw [hy] at hft
  apply P.t_ne_z
  have h1 : (f⁻¹ * w * (c * P.g)) * S.z * (f⁻¹ * w * (c * P.g))⁻¹ = P.t := by
    calc (f⁻¹ * w * (c * P.g)) * S.z * (f⁻¹ * w * (c * P.g))⁻¹
        = f⁻¹ * (w * ((c * P.g) * S.z * (c * P.g)⁻¹) * w⁻¹) * f := by group
      _ = f⁻¹ * (f * P.t * f⁻¹) * f := by rw [hy, hwy, hft]
      _ = P.t := by group
  rw [← h1]
  exact P.hW _ (h1 ▸ P.htQ)

omit [Finite G] in
theorem cl_t_ne_zero : S.cl P.t ≠ 0 := fun h => by
  rcases (S.cl_eq_zero_iff P.htQ).mp h with h' | h'
  · exact P.ht1 h'
  · exact P.t_ne_z h'

theorem commutator_ne_t {c : G} (hc : c ∈ S.QG) : P.x * c * P.x⁻¹ * c⁻¹ ≠ P.t := fun h =>
  P.conj_ne_t_mul_x c (by rw [P.conj_eq_commutator_mul hc, h])

omit [Finite G] in
theorem mem_conjBy_Qa_inv {a : G} (ha : a ∈ S.QG) : a ∈ (S.conjBy P.g).Qa P.g⁻¹ := by
  rw [(S.conjBy P.g).Qa_eq_map]
  refine ⟨P.g * a * P.g⁻¹, ?_, ?_⟩
  · change P.g * a * P.g⁻¹ ∈ S.Qa P.g
    rw [S.Qa_eq_map]
    exact ⟨a, ha, rfl⟩
  · change P.g⁻¹ * (P.g * a * P.g⁻¹) * P.g⁻¹⁻¹ = a
    group

@[expose] def swap : Pair (S.conjBy P.g) where
  g := P.g⁻¹
  t := P.t
  hW := P.hW.conjBy P.g
  hxM := by
    refine mem_centralizer_singleton_iff.mpr ?_
    change P.g⁻¹ * (P.g * S.z * P.g⁻¹) * P.g⁻¹⁻¹ * (P.g * S.z * P.g⁻¹) =
      (P.g * S.z * P.g⁻¹) * (P.g⁻¹ * (P.g * S.z * P.g⁻¹) * P.g⁻¹⁻¹)
    have e : P.g⁻¹ * (P.g * S.z * P.g⁻¹) * P.g⁻¹⁻¹ = S.z := by group
    rw [e, ← x_def]
    exact P.x_comm_z.symm
  hxz := by
    change P.g⁻¹ * (P.g * S.z * P.g⁻¹) * P.g⁻¹⁻¹ ≠ P.g * S.z * P.g⁻¹
    have e : P.g⁻¹ * (P.g * S.z * P.g⁻¹) * P.g⁻¹⁻¹ = S.z := by group
    rw [e, ← x_def]
    exact P.x_ne_z.symm
  htQ := P.hta
  hta := P.mem_conjBy_Qa_inv P.htQ
  ht1 := P.ht1

omit [Finite G] in
theorem swap_x : P.swap.x = S.z := by
  change P.g⁻¹ * (P.g * S.z * P.g⁻¹) * P.g⁻¹⁻¹ = S.z
  group

end Pair

end S63

end CFSG.LargeExtraspecial

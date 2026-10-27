module

public import CFSG.LargeExtraspecial.AS35TMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem commute_t_of_mem_pbar_YS (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) {b : G} (hb : b ∈ S.DSet) (hbM : b ∈ S.M)
    (hbP : S.ρ ⟨b, hbM⟩ ∈ S.PbarAsc g) : b * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * b := by
  refine S14.asc512FiveFiveStmt G S hS _ ht b hbM fun q hq => ?_
  have hw : g * S.z * g⁻¹ * q * (g * S.z * g⁻¹)⁻¹ * q⁻¹ ∈ S.QG :=
    S.QG.mul_mem (S.conj_mem_QG htM hq) (S.QG.inv_mem hq)
  have hcw : S.cl (g * S.z * g⁻¹ * q * (g * S.z * g⁻¹)⁻¹ * q⁻¹) ∈
      commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    refine mem_commSpace.mpr ⟨S.cl q, ?_⟩
    rw [S.cl_mul (S.conj_mem_QG htM hq) (S.QG.inv_mem hq), S.cl_inv hq]
    change S.rhoL htM (S.cl q) - S.cl q = _
    rw [S.rhoL_cl htM hq, sub_eq_add_vec (ZMod 2)]
  have hfix := AS35T.pbar_fix_commSpace hS ht htM hbP hcw
  change S.rhoL hbM _ = _ at hfix
  rw [S.rhoL_cl hbM hw] at hfix
  have h1 := S.conj_eq_of_cl_conj_eq hS.sixFour hS.weak hb hbM hw hfix
  calc b * (g * S.z * g⁻¹ * q * (g * S.z * g⁻¹)⁻¹ * q⁻¹)
      = b * (g * S.z * g⁻¹ * q * (g * S.z * g⁻¹)⁻¹ * q⁻¹) * b⁻¹ * b := by group
    _ = g * S.z * g⁻¹ * q * (g * S.z * g⁻¹)⁻¹ * q⁻¹ * b := by rw [h1]

theorem commute_x_YS (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet) {b x y u : G}
    (hxQ : x ∈ S.QG) (hyQt : y ∈ S.Qa g) (hbxy : b = x * y) (huQ : u ∈ S.QG)
    (hub : u * b = b * u) (hut : u * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * u) : u * x = x * u := by
  have hmem : x⁻¹ * u * x⁻¹⁻¹ * u⁻¹ ∈ S.Qa g := by
    have e : x⁻¹ * u * x⁻¹⁻¹ * u⁻¹ = y * (u * y⁻¹ * u⁻¹) := by
      have hb' : b⁻¹ * u * b = u := by
        calc b⁻¹ * u * b = b⁻¹ * (u * b) := by group
          _ = b⁻¹ * (b * u) := by rw [hub]
          _ = u := by group
      have hx : x = b * y⁻¹ := by rw [hbxy]; group
      rw [hx]
      calc (b * y⁻¹)⁻¹ * u * (b * y⁻¹)⁻¹⁻¹ * u⁻¹ = y * (b⁻¹ * u * b) * y⁻¹ * u⁻¹ := by group
        _ = y * (u * y⁻¹ * u⁻¹) := by rw [hb']; group
    rw [e]
    exact (S.Qa g).mul_mem hyQt (S.conj_mem_Qa_of_commute_asc hut ((S.Qa g).inv_mem hyQt))
  rcases S.commutator_eq_one_or_z (S.QG.inv_mem hxQ) huQ with h | h
  · calc u * x = x * (x⁻¹ * u * x⁻¹⁻¹ * u⁻¹) * u := by group
      _ = x * u := by rw [h, mul_one]
  · exact absurd (h ▸ hmem) (S.z_not_mem_Qa hS.weak (S.ne_z_of_mem_ESet ht.1))

theorem cl_mem_sup_YS (hS : S.SixHyp) {b t x : G} (hb : b ∈ S.DSet) (hbM : b ∈ S.M)
    (ht : t ∈ S.DSet) (htM : t ∈ S.M) (hxQ : x ∈ S.QG)
    (hx : ∀ u ∈ S.QG, u * b = b * u → u * t = t * u → u * x = x * u) :
    S.cl x ∈ commSpace (S.rhoL hbM) ⊔ commSpace (S.rhoL htM) := by
  have hbb := S.mul_self_of_isConj (S.isConj_of_mem_ESet hb.1)
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have hq := S.q_nondegenerate
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hq S.polarBilin_isRefl
    (commSpace (S.rhoL hbM) ⊔ commSpace (S.rhoL htM))]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
  have hvb : v ∈ fixSpace (S.rhoL hbM) := by
    rw [fixSpace_eq_orthogonal_commSpace hq (S.rhoL_mem hbM) (S.rhoL_mul_self hbM hbb),
      LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun n hn => hv n (Submodule.mem_sup_left hn)
  have hvt : v ∈ fixSpace (S.rhoL htM) := by
    rw [fixSpace_eq_orthogonal_commSpace hq (S.rhoL_mem htM) (S.rhoL_mul_self htM htt),
      LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun n hn => hv n (Submodule.mem_sup_right hn)
  obtain ⟨u, hu, rfl⟩ := S.exists_cl v
  have hub : b * u * b⁻¹ = u := by
    refine S.conj_eq_of_cl_conj_eq hS.sixFour hS.weak hb hbM hu ?_
    rw [← S.rhoL_cl hbM hu]
    exact mem_fixSpace.mp hvb
  have hut : t * u * t⁻¹ = u := by
    refine S.conj_eq_of_cl_conj_eq hS.sixFour hS.weak ht htM hu ?_
    rw [← S.rhoL_cl htM hu]
    exact mem_fixSpace.mp hvt
  have hcomm := hx u hu
    (calc u * b = b * u * b⁻¹ * b := by rw [hub]
      _ = b * u := by group)
    (calc u * t = t * u * t⁻¹ * t := by rw [hut]
      _ = t * u := by group)
  rw [QuadraticMap.polarBilin_apply_apply]
  exact (S.polar_cl_eq_zero_iff hu hxQ).mpr hcomm

theorem exists_mem_pbar_decomp_YS (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) {b : G} (hb : b ∈ S.DSet) (hbM : b ∈ S.M)
    (hbP : S.ρ ⟨b, hbM⟩ ∈ S.PbarAsc g) :
    ∃ y ∈ S.Qa g ⊓ S.M, ∃ d ∈ S.DSet, ∃ hdM : d ∈ S.M,
      S.ρ ⟨d, hdM⟩ = S.ρ ⟨b, hbM⟩ ∧ (y = d ∨ y = S.z * d) := by
  have hbt := commute_t_of_mem_pbar_YS hS ht htM hb hbM hbP
  obtain ⟨⟨y, hyM⟩, hyQt, hyb⟩ := (AS35T.mem_pbar_iff S).mp hbP
  have hxQ : b * y⁻¹ ∈ S.QG := by
    have e : (⟨b * y⁻¹, S.M.mul_mem hbM (S.M.inv_mem hyM)⟩ : S.M) = ⟨b, hbM⟩ * ⟨y, hyM⟩⁻¹ := rfl
    refine (S.ρ_eq_one_iff ⟨b * y⁻¹, S.M.mul_mem hbM (S.M.inv_mem hyM)⟩).mp ?_
    rw [e, map_mul, map_inv, hyb, mul_inv_cancel]
  have hbxy : b = b * y⁻¹ * y := by group
  have hcx : ∀ u ∈ S.QG, u * b = b * u → u * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * u →
      u * (b * y⁻¹) = b * y⁻¹ * u :=
    fun u hu hub hut => commute_x_YS hS ht hxQ hyQt hbxy hu hub hut
  have hcl := cl_mem_sup_YS hS hb hbM ht htM hxQ hcx
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hcl
  obtain ⟨w, rfl⟩ := mem_commSpace.mp ha
  obtain ⟨u, hu, rfl⟩ := S.exists_cl w
  obtain ⟨p, hp, hpc⟩ := AS35T.exists_mem_inf_Qa_cl_eq hS ht htM hc
  obtain ⟨hpQ, hpQt⟩ := mem_inf.mp hp
  have hbu : b * u * b⁻¹ ∈ S.QG := S.conj_mem_QG hbM hu
  have heQ : b * u * b⁻¹ * u⁻¹ ∈ S.QG := S.QG.mul_mem hbu (S.QG.inv_mem hu)
  have hcle : S.cl (b * u * b⁻¹ * u⁻¹ * p) = S.cl (b * y⁻¹) := by
    rw [← hac, S.cl_mul heQ hpQ, S.cl_mul hbu (S.QG.inv_mem hu), S.cl_inv hu, hpc,
      ← S.rhoL_cl hbM hu, sub_eq_add_vec (ZMod 2)]
  have huM : u ∈ S.M := S.QG_le_M hu
  have hdM : u * b * u⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem huM hbM) (S.M.inv_mem huM)
  have hρd : S.ρ ⟨u * b * u⁻¹, hdM⟩ = S.ρ ⟨b, hbM⟩ := by
    have e : (⟨u * b * u⁻¹, hdM⟩ : S.M) = ⟨u, huM⟩ * ⟨b, hbM⟩ * ⟨u, huM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, (S.ρ_eq_one_iff ⟨u, huM⟩).mpr hu, inv_one, one_mul,
      mul_one]
  have hpM : p ∈ S.M := S.QG_le_M hpQ
  refine ⟨p * y, mem_inf.mpr ⟨(S.Qa g).mul_mem hpQt hyQt, S.M.mul_mem hpM hyM⟩,
    u * b * u⁻¹, S.conj_mem_DSet huM hb, hdM, hρd, ?_⟩
  have hd : u * b * u⁻¹ = (b * u * b⁻¹ * u⁻¹)⁻¹ * b := by group
  rcases (S.cl_eq_cl_iff (S.QG.mul_mem heQ hpQ) hxQ).mp hcle with h | h
  · left
    rw [hd]
    calc p * y = (b * u * b⁻¹ * u⁻¹)⁻¹ * (b * u * b⁻¹ * u⁻¹ * p) * y := by group
      _ = (b * u * b⁻¹ * u⁻¹)⁻¹ * (b * y⁻¹) * y := by rw [h]
      _ = (b * u * b⁻¹ * u⁻¹)⁻¹ * b := by group
  · right
    have hpz : p * S.z = S.z * p := S.mem_M_iff.mp hpM
    rw [hd]
    calc p * y = S.z * (S.z * p) * y := by rw [← mul_assoc, S.z_mul_z, one_mul]
      _ = S.z * (p * S.z) * y := by rw [hpz]
      _ = S.z * ((b * u * b⁻¹ * u⁻¹)⁻¹ * (b * u * b⁻¹ * u⁻¹ * p * S.z) * y) := by group
      _ = S.z * ((b * u * b⁻¹ * u⁻¹)⁻¹ * (b * y⁻¹) * y) := by rw [h]
      _ = S.z * ((b * u * b⁻¹ * u⁻¹)⁻¹ * b) := by group

end Setting

end CFSG.LargeExtraspecial

module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalPlanes
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRealizers
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalPair

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open Module QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {b c : K}

private theorem exists_signed_perm_eq (v : Fin 3 → ZMod 3) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ ε : Fin 3 → ZMod 3,
      (∀ i, ε i ≠ 0) ∧ ε 0 * v (σ 0) = ε 1 * v (σ 1) := by
  revert v
  decide

private theorem signLE_commute_wExtend (ε : Fin 3 → ZMod 3)
    (g' : (K × K) ≃ₗ[K] (K × K)) : Commute (signLE K ε) (wExtend K g') := by
  refine (commute_iff_eq _ _).2 (LinearEquiv.ext fun x => ?_)
  refine Prod.ext (funext fun i => ?_) (Prod.ext ?_ ?_) <;>
    simp [LinearEquiv.mul_apply, signLE_apply, wExtend_apply]

private theorem permLE_commute_wExtend (σ : Equiv.Perm (Fin 3))
    (g' : (K × K) ≃ₗ[K] (K × K)) : Commute (permLE K σ) (wExtend K g') := by
  refine (commute_iff_eq _ _).2 (LinearEquiv.ext fun x => ?_)
  refine Prod.ext (funext fun i => ?_) (Prod.ext ?_ ?_) <;>
    simp [LinearEquiv.mul_apply, permLE_apply, wExtend_apply]

private theorem signLE_apply_wVec (ε : Fin 3 → ZMod 3) (q : K × K) :
    signLE K ε (wVec q) = wVec q := by
  refine Prod.ext (funext fun i => ?_) rfl
  simp [signLE_apply, wVec]

private theorem permLE_apply_wVec (σ : Equiv.Perm (Fin 3)) (q : K × K) :
    permLE K σ (wVec q) = wVec q := by
  refine Prod.ext (funext fun i => ?_) rfl
  simp [permLE_apply, wVec]

theorem exists_k7b_centralizer [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ plusPi (Nat.card K)) :
    ∃ y ∈ Subgroup.centralizer ((c₀ h3 hbc).range : Set ↥(omegaMinus8 K b c)), orderOf y = p ∧
      ∀ X : Subgroup ↥(omegaMinus8 K b c), X ≤ (c₀ h3 hbc).range → Nat.card X = 3 →
        ∃ u ∈ Subgroup.centralizer (X : Set ↥(omegaMinus8 K b c)), orderOf u = p ∧
          u * y = y * u ∧ u ∉ Subgroup.zpowers y := by
  classical
  obtain ⟨g, hg, hgord⟩ := exists_orderOf_eq_mem_orthogonalGroup_wForm h3 hbc hp hpd
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hgodd : Odd (orderOf g) := hgord ▸ hpodd
  have hy0 : wExtend K g ∈ modelOmega b c :=
    wExtend_mem_modelOmega_of_odd h3 hbc hg hgodd
  obtain ⟨m, hmO, hmord, hmcm, hmw, hmfix⟩ := exists_pairIsometry h3 hbc hg hp hp2 hgord
  refine ⟨(omegaEquiv (toModelIso h3 hbc)).symm ⟨wExtend K g, hy0⟩, ?_, ?_, ?_⟩
  ·
    have h := omegaEquiv_symm_mem_centralizer_c₀ h3 hbc (Set.univ) hy0
      (fun s _ => wExtend_commute_cmEquiv g (Multiplicative.toAdd s))
    rw [Set.image_univ, ← MonoidHom.coe_range] at h
    exact h
  ·
    rw [orderOf_omegaEquiv_symm (toModelIso h3 hbc) hy0, orderOf_wExtend, hgord]
  ·
    intro X hX hXcard
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hXcard])
    have hxord' : orderOf (x : ↥(omegaMinus8 K b c)) = 3 := by
      simpa using (Subgroup.orderOf_coe x).trans hxord
    have hXeq : X = Subgroup.zpowers (x : ↥(omegaMinus8 K b c)) := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2) ?_).symm
      rw [Nat.card_zpowers, hxord', hXcard]
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (hX x.2)
    set v : Fin 3 → ZMod 3 := Multiplicative.toAdd u with hvdef
    have hvu : Multiplicative.ofAdd v = u := rfl
    have hXv : X = Subgroup.zpowers (c₀ h3 hbc (Multiplicative.ofAdd v)) := by
      rw [hXeq, hvu, ← hu]
    obtain ⟨σ, ε, hε, hε01⟩ := exists_signed_perm_eq v
    set T : ModelSpace K ≃ₗ[K] ModelSpace K := signLE K ε * permLE K σ with hTdef
    have hTO : T ∈ modelO b c :=
      mul_mem (signLE_mem_modelO b c ε) (permLE_mem_modelO b c σ)
    have hTconj : T * cmEquiv K v * T⁻¹ =
        cmEquiv K (fun i => ε i * v (σ i)) := by
      rw [hTdef]
      calc (signLE K ε * permLE K σ) * cmEquiv K v * (signLE K ε * permLE K σ)⁻¹
          = signLE K ε * (permLE K σ * cmEquiv K v * (permLE K σ)⁻¹) *
              (signLE K ε)⁻¹ := by group
        _ = signLE K ε * cmEquiv K (fun i => v (σ i)) * (signLE K ε)⁻¹ := by
              rw [permLE_mul_cmEquiv_mul_inv]
        _ = cmEquiv K (fun i => ε i * v (σ i)) := by
              rw [signLE_mul_cmEquiv_mul_inv ε hε]
    have hTw : ∀ g' : (K × K) ≃ₗ[K] (K × K), Commute T (wExtend K g') := by
      intro g'
      rw [hTdef]
      exact (signLE_commute_wExtend ε g').mul_left (permLE_commute_wExtend σ g')
    have hTfix : ∀ q : K × K, T (wVec q) = wVec q := by
      intro q
      rw [hTdef]
      calc (signLE K ε * permLE K σ) (wVec q)
          = signLE K ε (permLE K σ (wVec q)) := rfl
        _ = signLE K ε (wVec q) := by rw [permLE_apply_wVec]
        _ = wVec q := signLE_apply_wVec ε q
    set u₀ : ModelSpace K ≃ₗ[K] ModelSpace K := T⁻¹ * m * T with hu₀def
    have hu₀O : u₀ ∈ modelO b c := mul_mem (mul_mem (inv_mem hTO) hmO) hTO
    have hu₀ord : orderOf u₀ = p := by
      have h : u₀ = (MulAut.conj T⁻¹) m := by
        rw [hu₀def, MulAut.conj_apply, inv_inv]
      rw [h, MulEquiv.orderOf_eq, hmord]
    have hu₀mem : u₀ ∈ modelOmega b c :=
      mem_modelOmega_of_odd h3 hbc hu₀O (hu₀ord ▸ hpodd)
    have hu₀fix : ∀ q : K × K, u₀ (wVec q) = wVec q := by
      intro q
      have hTinv : T⁻¹ (wVec q) = wVec q := by
        have h := congrArg (fun z => T⁻¹ z) (hTfix q)
        simpa using h.symm
      rw [hu₀def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hTfix q, hmfix q, hTinv]
    have hcmw : Commute m (cmEquiv K (fun i => ε i * v (σ i))) := hmcm _ hε01
    have hT' : T * cmEquiv K v = cmEquiv K (fun i => ε i * v (σ i)) * T := by
      rw [← hTconj]
      group
    have hu₀cm : Commute u₀ (cmEquiv K v) := by
      have hconj : u₀ * cmEquiv K v * u₀⁻¹ = cmEquiv K v := by
        rw [hu₀def]
        calc T⁻¹ * m * T * cmEquiv K v * (T⁻¹ * m * T)⁻¹
            = T⁻¹ * (m * (T * cmEquiv K v * T⁻¹) * m⁻¹) * T := by group
          _ = T⁻¹ * (m * cmEquiv K (fun i => ε i * v (σ i)) * m⁻¹) * T := by rw [hTconj]
          _ = T⁻¹ * cmEquiv K (fun i => ε i * v (σ i)) * T := by rw [hcmw.eq]; group
          _ = T⁻¹ * (T * cmEquiv K v * T⁻¹) * T := by rw [← hTconj]
          _ = cmEquiv K v := by group
      exact mul_inv_eq_iff_eq_mul.mp hconj
    have hu₀y : Commute u₀ (wExtend K g) := by
      rw [hu₀def]
      exact (((hTw g).symm.inv_right).symm.mul_left (hmw g)).mul_left (hTw g)
    refine ⟨(omegaEquiv (toModelIso h3 hbc)).symm ⟨u₀, hu₀mem⟩, ?_, ?_, ?_, ?_⟩
    ·
      have hS : ∀ s ∈ (Subgroup.zpowers (Multiplicative.ofAdd v) :
          Set (Multiplicative (Fin 3 → ZMod 3))), Commute u₀ (cm K s) := by
        intro s hs
        simp only [SetLike.mem_coe] at hs
        rw [Subgroup.mem_zpowers_iff] at hs
        obtain ⟨k, rfl⟩ := hs
        rw [map_zpow]
        exact hu₀cm.zpow_right k
      have hcen := omegaEquiv_symm_mem_centralizer_c₀ h3 hbc
        (Subgroup.zpowers (Multiplicative.ofAdd v)) hu₀mem hS
      have himg : ((c₀ h3 hbc) '' (Subgroup.zpowers (Multiplicative.ofAdd v) :
          Set (Multiplicative (Fin 3 → ZMod 3))) : Set ↥(omegaMinus8 K b c)) =
          (Subgroup.zpowers (c₀ h3 hbc (Multiplicative.ofAdd v)) :
            Set ↥(omegaMinus8 K b c)) := by
        ext z
        simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_zpowers_iff]
        constructor
        · rintro ⟨s, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, (map_zpow (c₀ h3 hbc) (Multiplicative.ofAdd v) k).symm⟩
        · rintro ⟨k, rfl⟩
          exact ⟨(Multiplicative.ofAdd v) ^ k, ⟨k, rfl⟩,
            map_zpow (c₀ h3 hbc) (Multiplicative.ofAdd v) k⟩
      rw [himg] at hcen
      rw [hXv]
      exact hcen
    ·
      rw [orderOf_omegaEquiv_symm (toModelIso h3 hbc) hu₀mem, hu₀ord]
    ·
      exact ((commute_omegaEquiv_symm_iff (toModelIso h3 hbc) hu₀mem hy0).2 hu₀y).eq
    ·
      intro hmem
      rw [omegaEquiv_symm_mem_zpowers_iff (toModelIso h3 hbc) hy0 hu₀mem] at hmem
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨k, hk⟩ := hmem
      have hmap : wExtend K (g ^ k) = u₀ := by
        rw [map_zpow]
        exact hk
      have hfixq : ∀ q : K × K, (g ^ k) q = q := by
        intro q
        have h : wExtend K (g ^ k) (wVec q) = wVec q := by rw [hmap, hu₀fix q]
        rw [wExtend_apply_wVec] at h
        simpa [wVec] using congrArg Prod.snd h
      have hg1 : g ^ k = 1 := LinearEquiv.ext hfixq
      have hu₀1 : u₀ = 1 := by rw [← hmap, hg1, map_one]
      rw [hu₀1, orderOf_one] at hu₀ord
      exact (Nat.ne_of_lt hp.one_lt) hu₀ord

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

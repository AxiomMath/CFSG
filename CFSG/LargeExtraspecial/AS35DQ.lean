module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S3Thompson
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem exists_singular_polar_eq_one (hn : 2 ≤ S.width) {v : S.Qt} (hv : v ≠ 0) :
    ∃ w : S.Qt, S.q w = 0 ∧ polar S.q w v = 1 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hnd := S.q_nondegenerate
  have hone : ∀ u : S.Qt, u ≠ 0 → ∃ n, polar S.q u n = 1 := by
    intro u hu
    by_contra! h
    refine hu (hnd.1 u fun n => ?_)
    rw [polarBilin_apply_apply]
    rcases zmod2_cases (polar S.q u n) with h' | h'
    · exact h'
    · exact absurd h' (h n)
  obtain ⟨y, hy⟩ : ∃ y, polar S.q y v = 1 := by
    obtain ⟨n, hn'⟩ := hone v hv
    exact ⟨n, by rw [polar_comm]; exact hn'⟩
  by_contra! hall
  have hns : ∀ w, polar S.q w v = 1 → S.q w = 1 := by
    intro w hw
    rcases zmod2_cases (S.q w) with h | h
    · exact absurd hw (hall w h)
    · exact h
  have hW : ∀ u, polar S.q u v = 0 → polar S.q u y = 0 → S.q u = 0 := by
    intro u hu1 hu2
    have h1 := hns (y + u) (by rw [polar_add_left, hy, hu1, add_zero])
    rw [QuadraticMap.map_add S.q y u, hns y hy, polar_comm, hu2, add_zero] at h1
    rcases zmod2_cases (S.q u) with h | h
    · exact h
    · rw [h] at h1
      exact absurd h1 (by decide)
  have hiso : ∀ u₁ u₂, polar S.q u₁ v = 0 → polar S.q u₁ y = 0 → polar S.q u₂ v = 0 →
      polar S.q u₂ y = 0 → polar S.q u₁ u₂ = 0 := by
    intro u₁ u₂ h1 h2 h3 h4
    have h5 := hW (u₁ + u₂) (by rw [polar_add_left, h1, h3, add_zero])
      (by rw [polar_add_left, h2, h4, add_zero])
    rw [QuadraticMap.map_add S.q u₁ u₂, hW u₁ h1 h2, hW u₂ h3 h4, zero_add, zero_add] at h5
    exact h5
  let φ : S.Qt →ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
    LinearMap.prod (S.q.polarBilin.flip v) (S.q.polarBilin.flip y)
  have hker : LinearMap.ker φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_prod, Module.finrank_self, S.finrank_Qt_eq_two_mul_width]
    omega)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hwv : polar S.q w v = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp hw)
  have hwy : polar S.q w y = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp hw)
  obtain ⟨n, hn1⟩ := hone w hw0
  set a := polar S.q n y
  set b := polar S.q n v
  have hvv : polar S.q v v = 0 := by
    have := S.polarBilin_isAlt v
    rwa [polarBilin_apply_apply] at this
  have hyy : polar S.q y y = 0 := by
    have := S.polarBilin_isAlt y
    rwa [polarBilin_apply_apply] at this
  have hvy : polar S.q v y = 1 := by rw [polar_comm]; exact hy
  have h1 : polar S.q (n + a • v + b • y) v = 0 := by
    rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hvv, hy, smul_zero,
      add_zero, smul_eq_mul, mul_one]
    exact CharTwo.add_self_eq_zero b
  have h2 : polar S.q (n + a • v + b • y) y = 0 := by
    rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hvy, hyy, smul_zero,
      add_zero, smul_eq_mul, mul_one]
    exact CharTwo.add_self_eq_zero a
  have h3 := hiso w (n + a • v + b • y) hwv hwy h1 h2
  rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, hwv, hwy, hn1,
    smul_zero, smul_zero, add_zero, add_zero] at h3
  exact absurd h3 (by decide)

theorem exists_involution_not_commute (hn : 2 ≤ S.width) {x : G} (hx : x ∈ S.QG) (hx1 : x ≠ 1)
    (hxz : x ≠ S.z) : ∃ u ∈ S.QG, u * u = 1 ∧ u * x ≠ x * u := by
  have hv : S.cl x ≠ 0 := by
    rw [ne_eq, S.cl_eq_zero_iff hx]
    rintro (h | h)
    · exact hx1 h
    · exact hxz h
  obtain ⟨w, hw0, hw1⟩ := S.exists_singular_polar_eq_one hn hv
  obtain ⟨u, hu, rfl⟩ := S.exists_cl w
  refine ⟨u, hu, ?_, (S.polar_cl_eq_one_iff hu hx).mp hw1⟩
  rw [← pow_two]
  exact (S.q_cl_eq_zero_iff hu).mp hw0

theorem exists_noncentral_involution (hn : 2 ≤ S.width) :
    ∃ t ∈ S.QG, t * t = 1 ∧ t ≠ 1 ∧ t ≠ S.z := by
  obtain ⟨y, hy, hyz⟩ := S.exists_sq_eq_z
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [one_pow] at hyz
    exact S.z_ne_one hyz.symm
  have hyz' : y ≠ S.z := by
    rintro rfl
    rw [S.z_sq] at hyz
    exact S.z_ne_one hyz.symm
  obtain ⟨u, hu, hu2, huy⟩ := S.exists_involution_not_commute hn hy hy1 hyz'
  refine ⟨u, hu, hu2, ?_, ?_⟩
  · rintro rfl
    exact huy (by group)
  · rintro rfl
    exact huy (S.z_comm_QG hy).symm

theorem QG_le_of_involutions (hn : 2 ≤ S.width) {N : Subgroup G}
    (hN : ∀ u ∈ S.QG, u * u = 1 → u ∈ N) : S.QG ≤ N := by
  intro x hx
  by_cases hxx : x * x = 1
  · exact hN x hx hxx
  have hx2 : x ^ 2 = S.z := (S.sq_eq_one_or_z hx).resolve_left (by rwa [pow_two])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxx (mul_one 1)
  have hxz : x ≠ S.z := by
    rintro rfl
    exact hxx S.z_mul_z
  obtain ⟨u, hu, hu2, hux⟩ := S.exists_involution_not_commute hn hx hx1 hxz
  have hc : u * x = S.z * (x * u) := (S.mul_comm_or hu hx).resolve_left hux
  have hxu : x * u * (x * u) = 1 := by
    calc x * u * (x * u) = x * (u * x) * u := by group
      _ = x * (S.z * (x * u)) * u := by rw [hc]
      _ = S.z * (x * x) * (u * u) := by
          rw [show x * (S.z * (x * u)) * u = (x * S.z) * x * (u * u) by group,
            S.z_comm_QG hx]
          group
      _ = 1 := by rw [hu2, ← pow_two, hx2, S.z_mul_z, mul_one]
  have h := N.mul_mem (hN _ (S.QG.mul_mem hx hu) hxu) (hN u hu hu2)
  rwa [mul_assoc, hu2, mul_one] at h

omit [Finite G] in
theorem centralizer_QG_eq : centralizer (S.QG : Set G) = zpowers S.z := by
  refine le_antisymm (fun c hc => ?_) ?_
  · have hc' : ∀ h ∈ S.QG, h * c = c * h := fun h hh => mem_centralizer_iff.mp hc h hh
    have hcM : c ∈ S.M := S.mem_M_iff.mpr (hc' S.z S.z_mem_QG).symm
    have hcQ : c ∈ S.QG := S.mem_QG_of_commute hcM fun x hx => (hc' x hx).symm
    rw [← S.QG_inf_centralizer_eq_zpowers]
    exact mem_inf.mpr ⟨hcQ, hc⟩
  · rw [zpowers_le, mem_centralizer_iff]
    intro h hh
    exact S.z_comm_QG hh

omit [Finite G] in
theorem eq_z_of_commute_QG {x : G} (hx : ∀ q ∈ S.QG, q * x = x * q) (hx1 : x ≠ 1) :
    x = S.z := by
  have hxc : x ∈ centralizer (S.QG : Set G) := mem_centralizer_iff.mpr hx
  rw [S.centralizer_QG_eq, mem_zpowers_iff_of_mul_self S.z_mul_z] at hxc
  exact hxc.resolve_left hx1

theorem z_mem_of_normalized {K : Subgroup G} (hK : ∀ q ∈ S.QG, ∀ k ∈ K, q * k * q⁻¹ ∈ K)
    (hev : Even (Nat.card K)) : S.z ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S.QG K :=
    { smul := fun q k => ⟨q * k * q⁻¹, hK q q.2 k k.2⟩
      one_smul := fun k => by
        apply Subtype.ext
        change (1 : G) * k * 1⁻¹ = k
        group
      mul_smul := fun a b k => by
        apply Subtype.ext
        change (a * b : G) * k * (a * b : G)⁻¹ = a * (b * k * (b : G)⁻¹) * (a : G)⁻¹
        group }
  have hmod := S.isPGroup_QG.card_modEq_card_fixedPoints K
  have hfix : Even (Nat.card (MulAction.fixedPoints S.QG K)) := by
    have h1 : Nat.card K % 2 = 0 := Nat.even_iff.mp hev
    unfold Nat.ModEq at hmod
    rw [hmod] at h1
    exact Nat.even_iff.mpr h1
  have h1fix : (1 : K) ∈ MulAction.fixedPoints S.QG K := fun q => by
    apply Subtype.ext
    change (q : G) * 1 * (q : G)⁻¹ = 1
    group
  obtain ⟨k, hk, hk1⟩ : ∃ k ∈ MulAction.fixedPoints S.QG K, k ≠ 1 := by
    by_contra! h
    have hsub : MulAction.fixedPoints S.QG K = {1} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨h1fix, h⟩
    rw [hsub, Nat.card_unique] at hfix
    exact absurd hfix (by decide)
  have hkz : (k : G) = S.z := by
    refine S.eq_z_of_commute_QG (fun q hq => ?_) fun h => hk1 (Subtype.ext h)
    have h := congrArg Subtype.val (hk ⟨q, hq⟩)
    change q * (k : G) * q⁻¹ = k at h
    calc q * (k : G) = q * k * q⁻¹ * q := by group
      _ = k * q := by rw [h]
  rw [← hkz]
  exact k.2

theorem even_card_of_le_QG {N : Subgroup G} (hNQ : N ≤ S.QG) (hN : N ≠ ⊥) :
    Even (Nat.card N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (S.isPGroup_QG.to_le hNQ)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hN (Subgroup.eq_bot_of_card_eq N hk)
  rw [hk]
  exact (Nat.even_pow' hk0).mpr even_two

theorem z_mem_of_le_M {N : Subgroup G} (hNM : N ≤ S.M)
    (hNQ : ∀ q ∈ S.QG, ∀ n ∈ N, q * n * q⁻¹ ∈ N) (hN : N ≠ ⊥) : S.z ∈ N := by
  have hN0 : N ⊓ S.QG ≠ ⊥ := by
    intro h0
    apply hN
    rw [eq_bot_iff]
    intro n hn
    have hcomm : ∀ q ∈ S.QG, n * q = q * n := by
      intro q hq
      have h1 : q * n * q⁻¹ * n⁻¹ ∈ N ⊓ S.QG := by
        refine mem_inf.mpr ⟨N.mul_mem (hNQ q hq n hn) (N.inv_mem hn), ?_⟩
        rw [show q * n * q⁻¹ * n⁻¹ = q * (n * q⁻¹ * n⁻¹) by group]
        exact S.QG.mul_mem hq (S.conj_mem_QG (hNM hn) (S.QG.inv_mem hq))
      rw [h0, mem_bot] at h1
      calc n * q = (q * n * q⁻¹ * n⁻¹)⁻¹ * (q * n) := by group
        _ = q * n := by rw [h1, inv_one, one_mul]
    have hnQ : n ∈ S.QG := S.mem_QG_of_commute (hNM hn) hcomm
    have : n ∈ N ⊓ S.QG := mem_inf.mpr ⟨hn, hnQ⟩
    rwa [h0] at this
  have hz := S.z_mem_of_normalized (K := N ⊓ S.QG)
    (fun q hq k hk => mem_inf.mpr ⟨hNQ q hq k (mem_inf.mp hk).1,
      S.conj_mem_QG (S.QG_le_M hq) (mem_inf.mp hk).2⟩)
    (S.even_card_of_le_QG inf_le_right hN0)
  exact (mem_inf.mp hz).1

theorem map_center_eq_zpowers {T : Subgroup G} (hT : IsPGroup 2 T) (hQT : S.QG ≤ T) :
    (center T).map T.subtype = zpowers S.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : (center T).map T.subtype ≤ zpowers S.z := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← S.centralizer_QG_eq, mem_centralizer_iff]
    intro q hq
    have := mem_center_iff.mp hc ⟨q, hQT hq⟩
    exact congrArg Subtype.val this
  have : Nontrivial T := ⟨⟨⟨S.z, hQT S.z_mem_QG⟩, 1, fun h => S.z_ne_one (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc, hc1⟩ := (Subgroup.nontrivial_iff_exists_ne_one (center T)).mp hT.center_nontrivial
  have hcz : (c : G) = S.z := by
    have := hsub ⟨c, hc, rfl⟩
    rw [mem_zpowers_iff_of_mul_self S.z_mul_z] at this
    exact this.resolve_left fun h => hc1 (Subtype.ext h)
  refine le_antisymm hsub ?_
  rw [zpowers_le, ← hcz]
  exact ⟨c, hc, rfl⟩

theorem le_M_of_isPGroup {T : Subgroup G} (hT : IsPGroup 2 T) (hQT : S.QG ≤ T) : T ≤ S.M := by
  have hz : S.z ∈ (center T).map T.subtype := by
    rw [S.map_center_eq_zpowers hT hQT]
    exact mem_zpowers _
  obtain ⟨c, hc, hcz⟩ := hz
  intro t ht
  rw [S.mem_M_iff, ← hcz]
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨t, ht⟩)

theorem exists_sylow_le_M : ∃ P : Sylow 2 G, S.QG ≤ P ∧ (P : Subgroup G) ≤ S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := S.isPGroup_QG.exists_le_sylow
  exact ⟨P, hP, S.le_M_of_isPGroup P.isPGroup' hP⟩

omit [Finite G] in
theorem exists_conj_eq_mul_z' {t : G} (ht : t ∈ S.QG) (ht1 : t ≠ 1) (htz : t ≠ S.z) :
    ∃ q ∈ S.QG, q * t * q⁻¹ = t * S.z := by
  obtain ⟨q, hq, hqt⟩ : ∃ q ∈ S.QG, q * t ≠ t * q := by
    by_contra! h
    rcases S.eq_one_or_z_of_commute ht fun y hy => (h y hy).symm with h1 | h1
    · exact ht1 h1
    · exact htz h1
  refine ⟨q, hq, ?_⟩
  have hc : q * t = S.z * (t * q) := (S.mul_comm_or hq ht).resolve_left hqt
  calc q * t * q⁻¹ = S.z * (t * q) * q⁻¹ := by rw [hc]
    _ = S.z * t := by group
    _ = t * S.z := (S.z_comm_QG ht).symm

theorem isConj_iff_exists_le_conj {t : G} (ht : t ∈ S.QG) (ht1 : t ≠ 1) (htz : t ≠ S.z) :
    IsConj S.z t ↔ ∃ g : G, g ∉ S.M ∧
      ∀ x ∈ S.QG, x * t = t * x → x * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * x := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    refine ⟨g, fun hgM => htz ?_, fun x _ hx => by rw [hg]; exact hx⟩
    rw [← hg, S.mem_M_iff.mp hgM]
    group
  · rintro ⟨g, hgM, hg⟩
    by_contra hnc
    set a := g * S.z * g⁻¹ with ha
    have ha2 : a ^ 2 = 1 := by
      rw [ha, pow_two, show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ by group,
        S.z_mul_z]
      group
    have haQ : a ∈ S.QG :=
      S.mem_QG_of_sq_eq_one_of_commute inf_le_left (S.relIndex_centralizer_eq_two ht ht1 htz)
        ha2 fun f hf => (hg f (mem_inf.mp hf).1
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hf).2)).symm
    have haC : a ∈ S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({t} : Set G) : Subgroup G) :
        Set G) := by
      refine mem_inf.mpr ⟨haQ, mem_centralizer_iff.mpr fun f hf => ?_⟩
      exact hg f (mem_inf.mp hf).1 (mem_centralizer_singleton_iff.mp (mem_inf.mp hf).2)
    rcases (S.mem_centralizer_centralizer_iff ht).mp haC with h | h | h | h
    · have h' : g * S.z * g⁻¹ = 1 := h
      have : S.z = 1 := by
        calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
          _ = 1 := by rw [h']; group
      exact S.z_ne_one this
    · apply hgM
      rw [S.mem_M_iff]
      have h' : g * S.z * g⁻¹ = S.z := h
      calc g * S.z = g * S.z * g⁻¹ * g := by group
        _ = S.z * g := by rw [h']
    · exact hnc (isConj_iff.mpr ⟨g, h⟩)
    · obtain ⟨q, hq, hqt⟩ := S.exists_conj_eq_mul_z' ht ht1 htz
      apply hnc
      refine isConj_iff.mpr ⟨q⁻¹ * g, ?_⟩
      rw [show q⁻¹ * g * S.z * (q⁻¹ * g)⁻¹ = q⁻¹ * (g * S.z * g⁻¹) * q by group]
      change q⁻¹ * a * q = t
      rw [h, ← hqt]
      group

end Setting

end CFSG.LargeExtraspecial

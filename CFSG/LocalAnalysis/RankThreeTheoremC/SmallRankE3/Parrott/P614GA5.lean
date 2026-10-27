module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GTrans
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GAlt
public import CFSG.GH74.GLS.C3.Layer1.Th2L83Alt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open scoped Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {M B H S K : Subgroup G} {z : G}

theorem mem_core_of_inner (c : Ctx M B H S K z) (hR0 : kRad H S K = pCoreOf 2 H) {s : G}
    (hs : s ∈ S)
    (h : c.rho ⟨s, c.S_le hs⟩ ∈ (MulAut.conj : Kbar K →* MulAut (Kbar K)).range) :
    s ∈ pCoreOf 2 H := by
  rw [← hR0]
  exact ⟨hs, c.mem_sup_of_inner hs h⟩

@[expose] noncomputable def sigma (c : Ctx M B H S K z) :
    ↥H →* MulAut ↥(omegaCenter (pCoreOf 2 H)) :=
  (omegaCenter (pCoreOf 2 H)).normalizerMonoidHom.comp (Subgroup.inclusion c.H_le_normalizer_V)

theorem sigma_apply (c : Ctx M B H S K z) (h : ↥H) (v : ↥(omegaCenter (pCoreOf 2 H))) :
    ((c.sigma h v : ↥(omegaCenter (pCoreOf 2 H))) : G) = (h : G) * v * (h : G)⁻¹ := by
  simp [sigma, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem sigma_eq_one_iff (c : Ctx M B H S K z) (h : ↥H) :
    c.sigma h = 1 ↔ (h : G) ∈ centralizer ((omegaCenter (pCoreOf 2 H) : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h1 v hv
    have := congrArg Subtype.val (congrArg (fun φ : MulAut _ => φ ⟨v, hv⟩) h1)
    simp only [MulAut.one_apply, c.sigma_apply] at this
    calc v * h = (h * v * (h : G)⁻¹) * h := by rw [this]
      _ = h * v := by group
  · intro h1
    ext v
    rw [c.sigma_apply, MulAut.one_apply, ← h1 v v.2]
    group

theorem mem_core_of_comm_sigma (c : Ctx M B H S K z) (hR0 : kRad H S K = pCoreOf 2 H)
    {k₀ g : G} (hk₀ : k₀ ∈ K) (hg : g ∈ S)
    (h : ∀ k (hk : k ∈ K), c.sigma ⟨k₀ * g, H.mul_mem (c.K_le hk₀) (c.S_le hg)⟩ *
      c.sigma ⟨k, c.K_le hk⟩ = c.sigma ⟨k, c.K_le hk⟩ *
        c.sigma ⟨k₀ * g, H.mul_mem (c.K_le hk₀) (c.S_le hg)⟩) :
    g ∈ pCoreOf 2 H := by
  have hyH : k₀ * g ∈ H := H.mul_mem (c.K_le hk₀) (c.S_le hg)
  have hrho : c.rho ⟨k₀ * g, hyH⟩ = 1 := by
    refine (c.rho_eq_one_iff hyH).2 fun k hk => ?_
    have hmem : k₀ * g * k * (k₀ * g)⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem (c.K_conj_mem hyH hk) (K.inv_mem hk)
    refine c.mem_core_of_mem_K_of_centralizer hmem ?_
    have e : (⟨k₀ * g * k * (k₀ * g)⁻¹ * k⁻¹, c.K_le hmem⟩ : ↥H) =
        ⟨k₀ * g, hyH⟩ * ⟨k, c.K_le hk⟩ * (⟨k₀ * g, hyH⟩ : ↥H)⁻¹ * (⟨k, c.K_le hk⟩ : ↥H)⁻¹ := rfl
    have h1 := (c.sigma_eq_one_iff ⟨_, c.K_le hmem⟩).1 (by
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h k hk]
      group)
    exact h1
  have hy := c.mem_core_of_trivial hyH hrho (mul_mem (mem_sup_left hk₀) (mem_sup_right hg))
  rw [← hR0]
  refine ⟨hg, ?_⟩
  have e : g = k₀⁻¹ * (k₀ * g) := by group
  rw [e]
  exact mul_mem (mem_sup_left (inv_mem hk₀)) (mem_sup_right hy)

@[expose] noncomputable def sigmaK (c : Ctx M B H S K z) :
    ↥K →* MulAut ↥(omegaCenter (pCoreOf 2 H)) :=
  c.sigma.comp (Subgroup.inclusion c.K_le)

@[expose] noncomputable def kPrime (c : Ctx M B H S K z) :
    Subgroup (MulAut ↥(omegaCenter (pCoreOf 2 H))) :=
  (K.subgroupOf H).map c.sigma

theorem sigmaK_range (c : Ctx M B H S K z) : c.sigmaK.range = c.kPrime := by
  ext φ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion c.K_le k, mem_subgroupOf.mpr k.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, mem_subgroupOf.mp hh⟩, rfl⟩

theorem sigma_mem_kPrime (c : Ctx M B H S K z) {k : G} (hk : k ∈ K) :
    c.sigma ⟨k, c.K_le hk⟩ ∈ c.kPrime :=
  ⟨⟨k, c.K_le hk⟩, mem_subgroupOf.mpr hk, rfl⟩

theorem sigmaK_ker (c : Ctx M B H S K z) : c.sigmaK.ker = CFSG.pPrimeCore 3 ↥K := by
  rw [c.pPrimeCore_eq]
  ext k
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  show c.sigma ⟨k, c.K_le k.2⟩ = 1 ↔ _
  rw [c.sigma_eq_one_iff]
  exact ⟨c.mem_core_of_mem_K_of_centralizer k.2, fun h => c.core_le_centralizer_V h⟩

@[expose] noncomputable def kbarEquiv (c : Ctx M B H S K z) : Kbar K ≃* ↥c.kPrime :=
  (QuotientGroup.quotientMulEquivOfEq c.sigmaK_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange c.sigmaK).trans (MulEquiv.subgroupCongr c.sigmaK_range))

theorem eq_bot_of_normal_two (c : Ctx M B H S K z) {Y : Type*} [Group Y] (e : Kbar K ≃* Y)
    (N : Subgroup Y) (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  have := c.isSimpleGroup
  have hN' : (N.map e.symm.toMonoidHom).Normal := hN.map _ e.symm.surjective
  rcases hN'.eq_bot_or_eq_top with h | h
  · rwa [map_eq_bot_iff_of_injective _ e.symm.injective] at h
  · exfalso
    have h2' : IsPGroup 2 (N.map e.symm.toMonoidHom) := h2.map _
    rw [h] at h2'
    obtain ⟨k, hk⟩ := h2' ⟨c.zbar, mem_top _⟩
    have hk' : c.zbar ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd := orderOf_dvd_of_pow_eq_one hk'
    rw [c.orderOf_zbar] at hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)

theorem nonempty_equiv_alt5 (c : Ctx M B H S K z) (hR0 : kRad H S K = pCoreOf 2 H)
    (hTr : KFactTransvRankOne) {a : G} (haS : a ∈ S) (haO : a ∉ pCoreOf 2 H)
    (hidx : (centralizer ({a} : Set G)).relIndex (omegaCenter (pCoreOf 2 H)) ≤ 2) :
    Nonempty (Kbar K ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := omegaCenter (pCoreOf 2 H) with hV
  haveI : IsMulCommutative ↥V := (isElemAbelian_omegaCenter _).1
  have haH : a ∈ H := c.S_le haS
  set τ := c.sigma ⟨a, haH⟩ with hτ
  set K' := c.kPrime with hK'
  have hτK : zpowers τ ≤ normalizer (K' : Set (MulAut ↥V)) := by
    rw [zpowers_le, mem_normalizer_iff]
    have key : ∀ (n : G) (hn : n ∈ H), ∀ φ ∈ K',
        c.sigma ⟨n, hn⟩ * φ * (c.sigma ⟨n, hn⟩)⁻¹ ∈ K' := by
      rintro n hn _ ⟨k, hk, rfl⟩
      have hk' : (n * k * n⁻¹ : G) ∈ K := c.K_conj_mem hn (mem_subgroupOf.mp hk)
      have e : c.sigma ⟨n, hn⟩ * c.sigma k * (c.sigma ⟨n, hn⟩)⁻¹ =
          c.sigma ⟨n * k * n⁻¹, c.K_le hk'⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact c.sigma_mem_kPrime hk'
    intro φ
    refine ⟨key a haH φ, fun h => ?_⟩
    have := key a⁻¹ (H.inv_mem haH) _ h
    have e : c.sigma ⟨a⁻¹, H.inv_mem haH⟩ = τ⁻¹ := by rw [hτ, ← map_inv]; rfl
    rw [e] at this
    simpa [mul_assoc] using this
  have hτnot : τ ∉ K' := by
    rintro ⟨k, hk, hkτ⟩
    have hkK : (k : G) ∈ K := mem_subgroupOf.mp hk
    refine haO (c.mem_core_of_comm_sigma hR0 (K.inv_mem hkK) haS fun k' hk' => ?_)
    have e : c.sigma ⟨(k : G)⁻¹ * a, H.mul_mem (c.K_le (K.inv_mem hkK)) haH⟩ = 1 := by
      have e1 : (⟨(k : G)⁻¹ * a, H.mul_mem (c.K_le (K.inv_mem hkK)) haH⟩ : ↥H) = k⁻¹ * ⟨a, haH⟩ :=
        rfl
      rw [e1, map_mul, map_inv, ← hτ, ← hkτ, inv_mul_cancel]
    rw [e, one_mul, mul_one]
  have hτ1 : τ ≠ 1 := fun h => hτnot (h ▸ K'.one_mem)
  have hK'simple : IsSimpleGroup ↥K' := c.kbarEquiv.isSimpleGroup_congr.mp c.isSimpleGroup
  set X := K' ⊔ zpowers τ with hX
  have hO2 : pCoreOf 2 X = ⊥ := by
    set N := pCoreOf 2 X with hN
    have hNX : N ≤ X := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X
    have hNn : X ≤ normalizer (N : Set (MulAut ↥V)) := localGroup_le_normalizer_pCoreOf 2 X
    have hK'X : K' ≤ X := le_sup_left
    have hK'n : X ≤ normalizer (K' : Set (MulAut ↥V)) := sup_le le_normalizer hτK
    have hNK : N ⊓ K' = ⊥ := by
      have h1 : (N ⊓ K').subgroupOf K' = ⊥ := by
        refine c.eq_bot_of_normal_two c.kbarEquiv _ ⟨fun n hn g => ?_⟩
          ((pCoreOf_isPGroup 2 X).to_le inf_le_left |>.comap_subtype)
        rw [mem_subgroupOf] at hn ⊢
        exact ⟨(mem_normalizer_iff.mp (hNn (hK'X g.2)) _).1 hn.1, K'.mul_mem (K'.mul_mem g.2 hn.2)
          (K'.inv_mem g.2)⟩
      rw [eq_bot_iff]
      intro φ hφ
      have : (⟨φ, hφ.2⟩ : ↥K') ∈ (N ⊓ K').subgroupOf K' := mem_subgroupOf.mpr hφ
      rw [h1, mem_bot] at this
      exact (mem_bot).mpr (congrArg Subtype.val this)
    rw [eq_bot_iff]
    intro n hn
    have hcomm : ∀ φ ∈ K', n * φ = φ * n := by
      intro φ hφ
      have h1 : n * φ * n⁻¹ * φ⁻¹ ∈ N ⊓ K' := by
        refine ⟨?_, ?_⟩
        · have := (mem_normalizer_iff.mp (hNn (hK'X hφ)) _).1 (inv_mem hn)
          have e : n * φ * n⁻¹ * φ⁻¹ = n * (φ * n⁻¹ * φ⁻¹) := by group
          rw [e]
          exact N.mul_mem hn this
        · exact K'.mul_mem ((mem_normalizer_iff.mp (hK'n (hNX hn)) _).1 hφ) (K'.inv_mem hφ)
      rw [hNK, mem_bot] at h1
      calc n * φ = (n * φ * n⁻¹ * φ⁻¹) * φ * n := by group
        _ = φ * n := by rw [h1, one_mul]
    have hnX := hNX hn
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K' (zpowers τ) hτK] at hnX
    obtain ⟨φ₀, ⟨k₀, hk₀, rfl⟩, ψ, hψ, rfl⟩ := Set.mem_mul.1 hnX
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hψ
    have hk₀K : (k₀ : G) ∈ K := mem_subgroupOf.mp hk₀
    have haj : a ^ j ∈ S := S.zpow_mem haS j
    have e : c.sigma k₀ * τ ^ j = c.sigma ⟨(k₀ : G) * a ^ j,
        H.mul_mem (c.K_le hk₀K) (c.S_le haj)⟩ := by
      rw [hτ, ← map_zpow, ← map_mul]
      rfl
    have hajO : a ^ j ∈ pCoreOf 2 H := by
      refine c.mem_core_of_comm_sigma hR0 hk₀K haj fun k hk => ?_
      rw [← e]
      exact hcomm _ (c.sigma_mem_kPrime hk)
    have hτj : τ ^ j = 1 := by
      have e2 : τ ^ j = c.sigma ⟨a ^ j, c.S_le haj⟩ := by
        rw [hτ, ← map_zpow]
        rfl
      rw [e2, c.sigma_eq_one_iff]
      exact c.core_le_centralizer_V hajO
    rw [hτj, mul_one] at hn ⊢
    have : c.sigma k₀ ∈ N ⊓ K' := ⟨hn, ⟨k₀, hk₀, rfl⟩⟩
    rw [hNK] at this
    exact this
  have hτtr : CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsTransvection τ := by
    refine ⟨hτ1, ?_⟩
    let f : ↥V →* ↥V :=
      { toFun := fun v => τ v * v⁻¹
        map_one' := by simp
        map_mul' := fun v w => by
          rw [map_mul, mul_inv, mul_mul_mul_comm] }
    have hfker : f.ker = (centralizer ({a} : Set G)).subgroupOf V := by
      ext v
      rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_singleton_iff]
      show τ v * v⁻¹ = 1 ↔ _
      rw [mul_inv_eq_one, Subtype.ext_iff, hτ, c.sigma_apply]
      constructor
      · intro h
        calc (v : G) * a = (a * v * a⁻¹) * a := by rw [h]
          _ = a * v := by group
      · intro h
        show a * v * a⁻¹ = v
        rw [← h]
        group
    have hcard : Nat.card f.range = 2 := by
      have hle : Nat.card f.range ≤ 2 := by
        rw [← index_ker, hfker]
        exact hidx
      have hne : f.range ≠ ⊥ := by
        intro hbot
        apply hτ1
        refine MulEquiv.ext fun v => ?_
        have : f v ∈ f.range := ⟨v, rfl⟩
        rw [hbot, mem_bot] at this
        have h2 : τ v * v⁻¹ = 1 := this
        rw [MulAut.one_apply]
        exact mul_inv_eq_one.mp h2
      have := (one_lt_card_iff_ne_bot f.range).mpr hne
      omega
    have hcl : Subgroup.closure (Set.range fun v : ↥V => τ v * v⁻¹) = f.range := by
      show Subgroup.closure (Set.range ⇑f) = f.range
      rw [← MonoidHom.coe_range]
      exact closure_eq _
    rw [hcl]
    exact hcard
  have hsq : ∀ v : ↥V, v * v = 1 := fun v => Subtype.ext (by
    simpa [pow_two] using (isElemAbelian_omegaCenter (pCoreOf 2 H)).2 v v.2)
  have hE : ∀ E : Subgroup (MulAut ↥V), E ≤ K' → IsElemAbelian 3 E → Nat.card E ≤ 3 := by
    intro E hEK hE
    have hE' : IsElemAbelian 3 (E.subgroupOf K') := by
      refine ⟨?_, fun x hx => Subtype.ext (by simpa using hE.2 _ (mem_subgroupOf.mp hx))⟩
      have := hE.1
      exact IsMulCommutative.of_setLike_mul_comm fun x hx y hy =>
        Subtype.ext (setLike_mul_comm (mem_subgroupOf.mp hx) (mem_subgroupOf.mp hy))
    have h1 := c.card_le_three c.kbarEquiv (E.subgroupOf K') hE'
    rwa [show Nat.card (E.subgroupOf K') = Nat.card E from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv] at h1
  obtain ⟨⟨e5⟩, -⟩ := hTr ↥V hsq X K' τ hO2 (mem_sup_right (mem_zpowers τ)) hτnot hτtr le_sup_left
    (normal_subgroupOf_sup_of_le_normalizer_left hτK) hK'simple
    (by
      obtain ⟨x, y, hxy⟩ := c.exists_ne_comm
      exact ⟨c.kbarEquiv x, c.kbarEquiv y, fun h => hxy (c.kbarEquiv.injective
        (by rw [map_mul, map_mul, h]))⟩)
    hE rfl
  exact ⟨c.kbarEquiv.trans e5⟩

theorem a5Case (c : Ctx M B H S K z) (hR0 : kRad H S K = pCoreOf 2 H)
    (ε : Kbar K ≃* alternatingGroup (Fin 5)) {a : G} (haS : a ∈ S) (haO : a ∉ pCoreOf 2 H) :
    A5Case H S K := by
  set α := CFSG.GH74.GLS.Th2.L83.altAut (by norm_num) (by norm_num) ε with hα
  have hKSH : K ⊔ S ≤ H := sup_le c.K_le c.S_le
  let f : ↥(K ⊔ S) →* Equiv.Perm (Fin 5) :=
    α.symm.toMonoidHom.comp (c.rho.comp (Subgroup.inclusion hKSH))
  have hf : ∀ y : ↥(K ⊔ S), f y = 1 ↔ c.rho ⟨y, hKSH y.2⟩ = 1 := fun y => by
    show α.symm (c.rho ⟨y, hKSH y.2⟩) = 1 ↔ _
    rw [map_eq_one_iff _ α.symm.injective]
  refine ⟨f, ?_, fun y => ?_⟩
  ·
    have hA5 : ∀ t ∈ alternatingGroup (Fin 5), ∃ y : ↥(K ⊔ S), f y = t := by
      intro t ht
      obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (ε.symm ⟨t, ht⟩)
      refine ⟨⟨k, mem_sup_left k.2⟩, ?_⟩
      show α.symm (c.rho ⟨k, c.K_le k.2⟩) = t
      rw [c.rho_of_mem_K k.2, show (QuotientGroup.mk ⟨(k : G), k.2⟩ : Kbar K) =
        QuotientGroup.mk k from rfl, hk, MulEquiv.symm_apply_eq, hα,
        CFSG.GH74.GLS.Th2.L83.altAut_eq_conj (t := ⟨t, ht⟩)]
    have hfa : f ⟨a, mem_sup_right haS⟩ ∉ alternatingGroup (Fin 5) := by
      intro hmem
      apply haO
      refine c.mem_core_of_inner hR0 haS ⟨ε.symm ⟨_, hmem⟩, ?_⟩
      have h1 := CFSG.GH74.GLS.Th2.L83.altAut_eq_conj (by norm_num) (by norm_num) ε ⟨_, hmem⟩
      rw [← hα] at h1
      rw [← h1]
      show α (α.symm (c.rho ⟨a, c.S_le haS⟩)) = _
      rw [MulEquiv.apply_symm_apply]
    intro σ'
    by_cases hσ : σ' ∈ alternatingGroup (Fin 5)
    · exact hA5 σ' hσ
    ·
      have hsign : Equiv.Perm.sign (σ' * (f ⟨a, mem_sup_right haS⟩)⁻¹) = 1 := by
        rw [Equiv.Perm.mem_alternatingGroup] at hσ hfa
        rw [map_mul, map_inv]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ') with h1 | h1
        · exact absurd h1 hσ
        · rcases Int.units_eq_one_or (Equiv.Perm.sign (f ⟨a, mem_sup_right haS⟩)) with h2 | h2
          · exact absurd h2 hfa
          · rw [h1, h2]
            decide
      obtain ⟨y, hy⟩ := hA5 _ (Equiv.Perm.mem_alternatingGroup.mpr hsign)
      refine ⟨y * ⟨a, mem_sup_right haS⟩, ?_⟩
      rw [map_mul, hy]
      group
  · rw [hf]
    constructor
    · intro h
      exact c.mem_core_of_trivial (hKSH y.2) h y.2
    · intro h
      exact c.rho_eq_one_of_mem_core h

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

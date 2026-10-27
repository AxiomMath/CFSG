module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Transport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem norm_decomposition {Γ M : Type*} [Group Γ] [Finite Γ] [CommGroup M]
    (act : Γ →* MulAut M) (H : Subgroup Γ) (hodd : ¬ 2 ∣ H.index) {z : M} (hz2 : z ^ 2 = 1)
    (hzH : ∀ x ∈ H, act x z = z) (N : Subgroup M) (hN : ∀ g : Γ, act g z * z⁻¹ ∈ N) :
    ∃ c u : M, z = c * u ∧ (∀ g, act g c = c) ∧ u ∈ N ∧ ∀ x ∈ H, act x u = u := by
  classical
  haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let f : Γ ⧸ H → M := fun q => act q.out z
  have hf : ∀ g : Γ, f (g : Γ ⧸ H) = act g z := by
    intro g
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul H g
    show act (g : Γ ⧸ H).out z = act g z
    rw [hx, map_mul]
    show act g (act (x : Γ) z) = act g z
    rw [hzH x x.2]
  have hsmul : ∀ (g : Γ) (q : Γ ⧸ H), act g (f q) = f (g • q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [hf a]
      have h1 : g • (a : Γ ⧸ H) = ((g * a : Γ) : Γ ⧸ H) := rfl
      rw [h1, hf (g * a), map_mul]
      rfl
  have hcfix : ∀ g : Γ, act g (∏ q : Γ ⧸ H, f q) = ∏ q : Γ ⧸ H, f q := by
    intro g
    rw [map_prod]
    simp_rw [hsmul]
    exact Equiv.prod_comp (MulAction.toPerm g) f
  have hcard : Fintype.card (Γ ⧸ H) = H.index := by
    rw [H.index_eq_card, Nat.card_eq_fintype_card]
  have hzidx : z ^ H.index = z := by
    obtain ⟨k, hk⟩ : Odd H.index := Nat.odd_iff.mpr (by omega)
    rw [hk, pow_succ, pow_mul, hz2, one_pow, one_mul]
  have hcw : ∏ q : Γ ⧸ H, f q = z * ∏ q : Γ ⧸ H, (f q * z⁻¹) := by
    have h1 : ∀ q : Γ ⧸ H, f q = z * (f q * z⁻¹) := fun q => by
      rw [mul_comm (f q), mul_inv_cancel_left]
    calc ∏ q : Γ ⧸ H, f q = ∏ q : Γ ⧸ H, (z * (f q * z⁻¹)) := Finset.prod_congr rfl fun q _ => h1 q
      _ = (∏ _q : Γ ⧸ H, z) * ∏ q : Γ ⧸ H, (f q * z⁻¹) := Finset.prod_mul_distrib
      _ = z * ∏ q : Γ ⧸ H, (f q * z⁻¹) := by
        rw [Finset.prod_const, Finset.card_univ, hcard, hzidx]
  have hwN : ∏ q : Γ ⧸ H, (f q * z⁻¹) ∈ N :=
    Subgroup.prod_mem N fun q _ => hN q.out
  refine ⟨∏ q : Γ ⧸ H, f q, (∏ q : Γ ⧸ H, (f q * z⁻¹))⁻¹, ?_, hcfix, N.inv_mem hwN, ?_⟩
  · rw [hcw, mul_inv_cancel_right]
  · intro x hx
    have hwinv : (∏ q : Γ ⧸ H, (f q * z⁻¹))⁻¹ = (∏ q : Γ ⧸ H, f q)⁻¹ * z := by
      rw [hcw, mul_inv_rev, inv_mul_cancel_right]
    rw [hwinv, map_mul, map_inv, hcfix x, hzH x hx]
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise commutatorElement

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

@[expose] noncomputable def trace_act (X E : Subgroup A) (hXE : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E) :
    ↥X →* MulAut ↥E where
  toFun x :=
    { toFun := fun e => ⟨(x : A) * e * (x : A)⁻¹, hXE x x.2 e e.2⟩
      invFun := fun e => ⟨(x : A)⁻¹ * e * (x : A), by
        have := hXE (x : A)⁻¹ (X.inv_mem x.2) e e.2
        simpa using this⟩
      left_inv := fun e => by ext; simp [mul_assoc]
      right_inv := fun e => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp [mul_assoc]

theorem trace_act_apply_coe (X E : Subgroup A) (hXE : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E)
    (x : ↥X) (e : ↥E) : ((trace_act X E hXE x e : ↥E) : A) = (x : A) * e * (x : A)⁻¹ := rfl

open scoped IsMulCommutative in
theorem trace_core {X H E N : Subgroup A} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hXE : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E)
    (hodd : ¬ 2 ∣ (H.subgroupOf X).index) {z : A} (hzE : z ∈ E) (hz2 : z ^ 2 = 1)
    (hzH : ∀ x ∈ H, x * z * x⁻¹ = z)
    (hN : ∀ g ∈ X, g * z * g⁻¹ * z⁻¹ ∈ N) :
    ∃ c u : A, c ∈ E ∧ u ∈ E ∧ z = c * u ∧ (∀ x ∈ X, x * c * x⁻¹ = c) ∧ u ∈ N ∧
      ∀ x ∈ H, x ∈ X → x * u * x⁻¹ = u := by
  haveI : IsMulCommutative ↥E := ⟨⟨fun a b => Subtype.ext (hE a a.2 b b.2)⟩⟩
  obtain ⟨c, u, hzcu, hc, hu, hH⟩ := norm_decomposition (trace_act X E hXE) (H.subgroupOf X) hodd
    (z := (⟨z, hzE⟩ : ↥E)) (Subtype.ext (by simpa using hz2))
    (fun x hx => Subtype.ext (hzH x (mem_subgroupOf.1 hx))) (N.subgroupOf E)
    (fun g => mem_subgroupOf.2 (by simpa [trace_act_apply_coe] using hN g g.2))
  exact ⟨c, u, c.2, u.2, congrArg Subtype.val hzcu,
    fun x hx => congrArg Subtype.val (hc ⟨x, hx⟩), mem_subgroupOf.1 hu,
    fun x hxH hxX => congrArg Subtype.val (hH ⟨x, hxX⟩ (mem_subgroupOf.2 hxH))⟩

theorem trace_conj_mem (x : A) (hx : x ∈ normalizer (pCoreOf 2 X : Set A)) {e : A}
    (he : e ∈ pCoreOf 2 X ⊓ centralizer (pCoreOf 2 X : Set A)) :
    x * e * x⁻¹ ∈ pCoreOf 2 X ⊓ centralizer (pCoreOf 2 X : Set A) := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hx e).1 he.1, mem_centralizer_iff.2 fun q hq => ?_⟩
  have hq' : x⁻¹ * q * x ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff''.1 hx q).1 hq
  have h1 : (x⁻¹ * q * x) * e = e * (x⁻¹ * q * x) := mem_centralizer_iff.1 he.2 _ hq'
  calc q * (x * e * x⁻¹) = x * ((x⁻¹ * q * x) * e) * x⁻¹ := by group
    _ = x * (e * (x⁻¹ * q * x)) * x⁻¹ := by rw [h1]
    _ = x * e * x⁻¹ * q := by group

theorem CampbellHyp.trace_decomposition (h : CampbellHyp X K R P) {z : A}
    (hz : z ∈ omegaCenter R) :
    ∃ c u : A, z = c * u ∧ (∀ x ∈ X, x * c * x⁻¹ = c) ∧
      u ∈ CFSG.Quasithin.c134Q X K ∧ (∀ r ∈ R, r * u * r⁻¹ = u) ∧
      (∀ q ∈ pCoreOf 2 X, q * u = u * q) := by
  obtain ⟨hzR, hzC, hz2⟩ := hz
  have hQR : pCoreOf 2 X ≤ R := h.pCore_X_le_R
  have hzcent : z ∈ centralizer (pCoreOf 2 X : Set A) :=
    mem_centralizer_iff.2 fun q hq => (hzC q (hQR hq)).symm
  have hzQ : z ∈ pCoreOf 2 X := h.charTwo ⟨h.R_le hzR, hzcent⟩
  obtain ⟨c, u, -, huE, hzcu, hc, hu, hR⟩ := trace_core
    (X := X) (H := R) (E := pCoreOf 2 X ⊓ centralizer (pCoreOf 2 X : Set A))
    (N := CFSG.Quasithin.c134Q X K)
    (fun a ha b hb => mem_centralizer_iff.1 hb.2 a ha.1)
    (fun x hx e he => trace_conj_mem x (normalizer_pCoreOf X hx) he) h.R_sylow
    (z := z) ⟨hzQ, hzcent⟩ hz2
    (fun x hx => by rw [← hzC x hx]; group)
    (fun g hg => by
      obtain ⟨k, hk, o, ho, rfl⟩ := h.mem_X_iff.1 hg
      have hoz : o * z = z * o := mem_centralizer_iff.1 hzcent o ho
      have hkz : ⁅k, z⁆ ∈ CFSG.Quasithin.c134Q X K := by
        rw [CFSG.Quasithin.c134Q, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hk hzQ
      have heq : k * o * z * (k * o)⁻¹ * z⁻¹ = ⁅k, z⁆ :=
        calc k * o * z * (k * o)⁻¹ * z⁻¹ = k * (o * z) * o⁻¹ * k⁻¹ * z⁻¹ := by group
          _ = k * (z * o) * o⁻¹ * k⁻¹ * z⁻¹ := by rw [hoz]
          _ = ⁅k, z⁆ := by rw [commutatorElement_def]; group
      rw [heq]
      exact hkz)
  exact ⟨c, u, hzcu, hc, hu, fun r hr => hR r hr (h.R_le hr),
    fun q hq => mem_centralizer_iff.1 huE.2 q hq⟩
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem sylowImage_relIndex_sup_right {R K : Subgroup A} (hR : R ≤ normalizer (K : Set A)) :
    K.relIndex (R ⊔ K) = K.relIndex R := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hR
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hR
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient R K hR).toEquiv.symm

theorem sylowImage_sup_eq (h : CampbellHyp X K R P) : R ⊔ K = X := by
  refine le_antisymm (sup_le h.R_le h.K_le) ?_
  calc X = K ⊔ pCoreOf 2 X := h.X_eq
    _ ≤ K ⊔ R := sup_le_sup_left h.pCore_X_le_R K
    _ = R ⊔ K := sup_comm _ _

theorem sylowImage_relIndex_eq (h : CampbellHyp X K R P) :
    (R ⊓ K).relIndex K = R.relIndex X := by
  have hRn : R ≤ normalizer (K : Set A) := h.R_le.trans h.K_normal
  have h1 : K.relIndex X = K.relIndex R := by
    rw [← sylowImage_sup_eq h]
    exact sylowImage_relIndex_sup_right hRn
  have h2 : (R ⊓ K).relIndex X = (R ⊓ K).relIndex R * R.relIndex X :=
    (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left h.R_le).symm
  have h3 : (R ⊓ K).relIndex X = (R ⊓ K).relIndex K * K.relIndex X :=
    (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right h.K_le).symm
  have h4 : (R ⊓ K).relIndex R = K.relIndex R := Subgroup.inf_relIndex_left R K
  have hne : K.relIndex R ≠ 0 := Subgroup.index_ne_zero_of_finite
  have key : K.relIndex R * R.relIndex X = K.relIndex R * (R ⊓ K).relIndex K := by
    rw [← h4, ← h2, h3, h1, h4, mul_comm]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) key).symm

theorem sylowImage_card_eq_eight {n i : ℕ} (hodd : ¬ 2 ∣ i) (hmul : 2 ^ n * i = 168) :
    2 ^ n = 8 := by
  have hn : n < 8 := by
    by_contra hcon
    have h1 : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
    have hi : 0 < i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [h0] at hmul; omega
      · exact h0
    have : 2 ^ n ≤ 2 ^ n * i := Nat.le_mul_of_pos_right _ hi
    omega
  interval_cases n <;> omega

theorem CampbellHyp.sylow_image_card (h : CampbellHyp X K R P) (a : ↥K →* GL32)
    (ha : Function.Surjective a) (hker : a.ker = CFSG.pCore 2 ↥K) :
    Nat.card ↥(((R ⊓ K).subgroupOf K).map a) = 8 := by
  have hS₀ : IsPGroup 2 ((R ⊓ K).subgroupOf K) := (h.R_two.to_le inf_le_left).comap_subtype
  have hS₂ : IsPGroup 2 (((R ⊓ K).subgroupOf K).map a) := hS₀.map a
  have hkerle : a.ker ≤ (R ⊓ K).subgroupOf K := by
    intro k hk
    rw [hker, h.pCore_K_eq] at hk
    exact mem_subgroupOf.2 ⟨h.pCore_X_le_R hk, k.2⟩
  have hidx : (((R ⊓ K).subgroupOf K).map a).index = (R ⊓ K).relIndex K :=
    Subgroup.index_map_eq _ ha hkerle
  have hodd : ¬ 2 ∣ (((R ⊓ K).subgroupOf K).map a).index := by
    rw [hidx, sylowImage_relIndex_eq h]
    exact h.R_sylow
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hS₂
  have hmul := Subgroup.card_mul_index (((R ⊓ K).subgroupOf K).map a)
  rw [CFSG.ComponentClassification.GHarris.card_GL32_gh, hn] at hmul
  rw [hn]
  exact sylowImage_card_eq_eight hodd hmul
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem stabIndex_ker_eq (h : CampbellHyp X K R P) {ψ : ↥X →* GL32}
    (hψker : ψ.ker = (pCoreOf 2 X).subgroupOf X) {a : ↥K →* GL32}
    (hker : a.ker = CFSG.pCore 2 ↥K) :
    (ψ.comp (Subgroup.inclusion h.K_le)).ker = a.ker := by
  rw [hker, h.pCore_K_eq]
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hψker]
  exact Iff.rfl

theorem stabIndex_surj (h : CampbellHyp X K R P) {ψ : ↥X →* GL32}
    (hψs : Function.Surjective ψ) (hψker : ψ.ker = (pCoreOf 2 X).subgroupOf X) :
    Function.Surjective (ψ.comp (Subgroup.inclusion h.K_le)) := by
  intro y
  obtain ⟨x, rfl⟩ := hψs y
  obtain ⟨k, hk, o, ho, hxko⟩ := h.mem_X_iff.1 x.2
  refine ⟨⟨k, hk⟩, ?_⟩
  have hxo : x = Subgroup.inclusion h.K_le ⟨k, hk⟩ * ⟨o, pCoreOf_le_self X ho⟩ :=
    Subtype.ext hxko
  have ho' : (⟨o, pCoreOf_le_self X ho⟩ : ↥X) ∈ ψ.ker := by
    rw [hψker]
    exact ho
  rw [MonoidHom.comp_apply]
  conv_rhs => rw [hxo]
  rw [map_mul, MonoidHom.mem_ker.1 ho', mul_one]

theorem stabIndex_map_eq (h : CampbellHyp X K R P) {ψ : ↥X →* GL32}
    (hψker : ψ.ker = (pCoreOf 2 X).subgroupOf X) (a : ↥K →* GL32) (e : Fin 3 → ZMod 2) :
    ((stabSub K a e (pCoreOf 2 X)).subgroupOf X).map ψ =
      ((vecStab e).comap a).map (ψ.comp (Subgroup.inclusion h.K_le)) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro s hs
    have hT : stabSub K a e (pCoreOf 2 X) ≤
        ((((vecStab e).comap a).map (ψ.comp (Subgroup.inclusion h.K_le))).comap ψ).map
          X.subtype := by
      refine sup_le ?_ ?_
      · rintro _ ⟨k, hk, rfl⟩
        exact ⟨Subgroup.inclusion h.K_le k, ⟨k, hk, rfl⟩, rfl⟩
      · intro q hq
        refine ⟨⟨q, pCoreOf_le_self X hq⟩, ?_, rfl⟩
        have hq' : (⟨q, pCoreOf_le_self X hq⟩ : ↥X) ∈ ψ.ker := by
          rw [hψker]
          exact hq
        rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.mem_ker.1 hq']
        exact one_mem _
    obtain ⟨t, ht, hts⟩ := hT hs
    have hts' : t = s := Subtype.ext hts
    rwa [hts'] at ht
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨Subgroup.inclusion h.K_le k, ?_, rfl⟩
    exact Subgroup.mem_sup_left ⟨k, hk, rfl⟩

theorem CampbellHyp.stabSub_index (h : CampbellHyp X K R P) (a : ↥K →* GL32)
    (ha : Function.Surjective a) (hker : a.ker = CFSG.pCore 2 ↥K) {e : Fin 3 → ZMod 2}
    (he : e ≠ 0) :
    stabSub K a e (pCoreOf 2 X) ≤ X ∧ ((stabSub K a e (pCoreOf 2 X)).subgroupOf X).index = 7 := by
  have hKe : ((vecStab e).comap a).map K.subtype ≤ X :=
    (Subgroup.map_subtype_le _).trans h.K_le
  refine ⟨sup_le hKe (pCoreOf_le_self X), ?_⟩
  obtain ⟨ψ, hψs, hψker⟩ := h.exists_psi
  have hS : ψ.ker ≤ (stabSub K a e (pCoreOf 2 X)).subgroupOf X := by
    rw [hψker]
    intro x hx
    exact Subgroup.mem_sup_right hx
  have hkerK : (ψ.comp (Subgroup.inclusion h.K_le)).ker ≤ (vecStab e).comap a := by
    rw [stabIndex_ker_eq h hψker hker]
    intro k hk
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hk]
    exact one_mem _
  rw [← Subgroup.index_map_eq _ hψs hS, stabIndex_map_eq h hψker,
    Subgroup.index_map_eq _ (stabIndex_surj h hψs hψker) hkerK,
    Subgroup.index_comap_of_surjective _ ha, index_vecStab he]
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem stabCent_normalizes_Q (h : CampbellHyp X K R P) :
    X ≤ normalizer ((CFSG.Quasithin.c134Q X K : Subgroup A) : Set A) :=
  normalizer_commutator_of_normalizes (normalizer_pCoreOf X) h.K_normal

theorem stabCent_conj_mem_Q (h : CampbellHyp X K R P) {x u : A} (hx : x ∈ X)
    (hu : u ∈ CFSG.Quasithin.c134Q X K) : x * u * x⁻¹ ∈ CFSG.Quasithin.c134Q X K :=
  (Subgroup.mem_normalizer_iff.1 (stabCent_normalizes_Q h hx) u).1 hu

theorem stabCent_comm_mul {x c u : A} (hc : x * c = c * x) (hu : x * u = u * x) :
    x * (c * u) = (c * u) * x := by
  rw [← mul_assoc, hc, mul_assoc, hu, mul_assoc]

theorem stabCent_conj_eq (h : CampbellHyp X K R P) (a : ↥K →* GL32)
    (b : ↥(CFSG.Quasithin.c134Q X K) →* Multiplicative (Fin 2 → Fin 3 → ZMod 2))
    (hinj : Function.Injective b)
    (hequiv : ∀ (k : ↥K) (u v : ↥(CFSG.Quasithin.c134Q X K)), (v : A) = k * u * k⁻¹ →
      ∀ i : Fin 2, Multiplicative.toAdd (b v) i =
        ((a k : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (b u) i))
    {e : Fin 3 → ZMod 2}
    (hline : ∀ v : Fin 3 → ZMod 2, (∀ s : ↥K, (s : A) ∈ R →
      ((a s : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) → v = 0 ∨ v = e)
    {u : A} (hu : u ∈ CFSG.Quasithin.c134Q X K) (hR : ∀ r ∈ R, r * u * r⁻¹ = u)
    (k : ↥K) (hk : a k ∈ vecStab e) : (k : A) * u * (k : A)⁻¹ = u := by
  have hv : (k : A) * u * (k : A)⁻¹ ∈ CFSG.Quasithin.c134Q X K :=
    stabCent_conj_mem_Q h (h.K_le k.2) hu
  have hcoord : ∀ i : Fin 2, Multiplicative.toAdd (b ⟨u, hu⟩) i = 0 ∨
      Multiplicative.toAdd (b ⟨u, hu⟩) i = e := by
    intro i
    apply hline
    intro s hs
    exact (hequiv s ⟨u, hu⟩ ⟨u, hu⟩ (hR s hs).symm i).symm
  have hfix : ∀ i : Fin 2, Multiplicative.toAdd (b ⟨(k : A) * u * (k : A)⁻¹, hv⟩) i =
      Multiplicative.toAdd (b ⟨u, hu⟩) i := by
    intro i
    rw [hequiv k ⟨u, hu⟩ ⟨(k : A) * u * (k : A)⁻¹, hv⟩ rfl i]
    rcases hcoord i with h0 | he
    · rw [h0, Matrix.mulVec_zero]
    · rw [he]
      exact hk
  have hbeq : b ⟨(k : A) * u * (k : A)⁻¹, hv⟩ = b ⟨u, hu⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    exact hfix i
  exact congrArg Subtype.val (hinj hbeq)

theorem CampbellHyp.stabSub_centralizes (h : CampbellHyp X K R P) (a : ↥K →* GL32)
    (b : ↥(CFSG.Quasithin.c134Q X K) →* Multiplicative (Fin 2 → Fin 3 → ZMod 2))
    (hinj : Function.Injective b)
    (hequiv : ∀ (k : ↥K) (u v : ↥(CFSG.Quasithin.c134Q X K)), (v : A) = k * u * k⁻¹ →
      ∀ i : Fin 2, Multiplicative.toAdd (b v) i =
        ((a k : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (b u) i))
    {e : Fin 3 → ZMod 2}
    (hline : ∀ v : Fin 3 → ZMod 2, (∀ s : ↥K, (s : A) ∈ R →
      ((a s : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) → v = 0 ∨ v = e) :
    ∀ z ∈ omegaCenter R, ∀ g ∈ stabSub K a e (pCoreOf 2 X), g * z = z * g := by
  intro z hz g hg
  obtain ⟨c, u, hzcu, hcX, huQ, huR, huQX⟩ := h.trace_decomposition hz
  have hS : ∀ k ∈ ((vecStab e).comap a).map K.subtype, k * z = z * k := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hk
    have hkX : (k' : A) ∈ X := h.K_le k'.2
    have hkc : (k' : A) * c = c * (k' : A) := mul_inv_eq_iff_eq_mul.1 (hcX _ hkX)
    have hku : (k' : A) * u = u * (k' : A) :=
      mul_inv_eq_iff_eq_mul.1 (stabCent_conj_eq h a b hinj hequiv hline huQ huR k' hk')
    rw [hzcu]
    exact stabCent_comm_mul hkc hku
  have hO : ∀ o ∈ pCoreOf 2 X, o * z = z * o := by
    intro o ho
    have hoX : o ∈ X := pCoreOf_le_self X ho
    have hoc : o * c = c * o := mul_inv_eq_iff_eq_mul.1 (hcX _ hoX)
    rw [hzcu]
    exact stabCent_comm_mul hoc (huQX o ho)
  have hle : stabSub K a e (pCoreOf 2 X) ≤ Subgroup.centralizer {z} := by
    refine sup_le (fun k hk => ?_) (fun o ho => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hS k hk).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hO o ho).symm
  exact (Subgroup.mem_centralizer_iff.1 (hle hg) z rfl).symm
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem centEq_eq_of_relIndex_eq {X P₂ P : Subgroup A} (hP₂P : P₂ ≤ P) (hPX : P ≤ X)
    (h₂ : P₂.relIndex X = 7) (h₁ : P.relIndex X = 7) : P₂ = P := by
  have hmul := Subgroup.relIndex_mul_relIndex P₂ P X hP₂P hPX
  rw [h₂, h₁] at hmul
  have h1 : P₂.relIndex P = 1 := by omega
  exact le_antisymm hP₂P (Subgroup.relIndex_eq_one.1 h1)

theorem CampbellHyp.centralizer_omegaCenter_eq (h : CampbellHyp X K R P)
    (hN : HasNatSum2 K (CFSG.Quasithin.c134Q X K)) :
    X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) = P := by
  obtain ⟨hKQ, a, b, ha, hker, hb, hinj, hequiv⟩ := hN
  obtain ⟨e, he, hfix⟩ := sylow_fixed_line (h.sylow_image_card a ha hker)
  have hline : ∀ v : Fin 3 → ZMod 2, (∀ s : ↥K, (s : A) ∈ R →
      ((a s : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) → v = 0 ∨ v = e := by
    intro v hv
    refine (hfix v).1 fun g hg => ?_
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hg
    exact hv s (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).1
  obtain ⟨hP₂X, hP₂idx⟩ := h.stabSub_index a ha hker he
  have hcent := h.stabSub_centralizes a b hinj hequiv hline
  have hP₂le : stabSub K a e (pCoreOf 2 X) ≤
      X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨hP₂X hg, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    exact (hcent z hz g hg).symm
  have hP₂P : stabSub K a e (pCoreOf 2 X) ≤ P := hP₂le.trans h.cent_le
  have hEq : stabSub K a e (pCoreOf 2 X) = P :=
    centEq_eq_of_relIndex_eq hP₂P h.P_le hP₂idx h.P_index
  refine le_antisymm h.cent_le ?_
  rw [← hEq]
  exact hP₂le
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem CampbellHyp.not_isC134Case2 (h : CampbellHyp X K R P) :
    ¬ CFSG.Quasithin.IsC134Case2 X (pCoreOf 2 P) K := by
  rintro ⟨⟨n, F, _, _, α, hF, hα, hsec⟩, hNot⟩
  have hF2 := h.card_field_eq_two hF α hα
  have hN := h.centralizer_omegaCenter_eq (hasNatSum2_of_via hF2 hα hsec)
  have := hNot R ⟨h.R_le, h.R_two, h.R_sylow⟩ h.pCore_P_le_R
  rw [omegaOneCenterOf_eq_omegaCenter, hN] at this
  exact this rfl
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

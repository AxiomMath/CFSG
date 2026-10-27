module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelPointMeet
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeRootSub
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeStab

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.OrthogonalInvolutions QuadraticMap Module

section LineFixed

variable {K' : Type} [Field K'] [CharP K' 2] [Finite K'] {N : Type} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N}

private theorem exists_fixed_pair_of_stable {L : Subgroup ↥(elementaryGroup QN)}
    (hL : IsPGroup 2 L) {U : Submodule K' N} (hU2 : finrank K' U = 2)
    (hU : ∀ g ∈ L, ∀ x ∈ U, (g : N ≃ₗ[K'] N) x ∈ U) :
    ∃ e ∈ U, e ≠ 0 ∧ (∀ g ∈ L, (g : N ≃ₗ[K'] N) e = e) ∧
      ∃ p ∈ U, p ∉ K' ∙ e ∧ ∀ g ∈ L, ∃ c : K', (g : N ≃ₗ[K'] N) p = p + c • e := by
  have : Finite N := Module.finite_of_finite K'
  have hlin := isLinearAction_Gom QN
  have hne : (⊥ : Submodule K' N) ≠ U := fun h => by
    rw [← h, finrank_bot] at hU2
    omega
  obtain ⟨e, heU, he0, hfix⟩ := CFSG.ClassicalGroups.PCoreSection.exists_fixed_mem_of_isPGroup hlin
    (T := L) hL (L := (⊥ : Submodule K' N)) (P := U) bot_le hU
    (fun t _ x hx => by
      rw [(Submodule.mem_bot K' (M := N)).mp hx]
      exact (Submodule.mem_bot K' (M := N)).mpr (Gom.app_zero t)) hne
  have hefix : ∀ g ∈ L, (g : N ≃ₗ[K'] N) e = e := fun g hg => by
    have := hfix g hg
    rwa [Submodule.mem_bot, sub_eq_zero] at this
  refine ⟨e, heU, fun h => he0 (by rw [h]; exact Submodule.zero_mem _), hefix, ?_⟩
  have hsp : K' ∙ e ≤ U := Submodule.span_le.mpr (by simpa using heU)
  have hne' : K' ∙ e ≠ U := fun h => by
    have h1 : finrank K' (K' ∙ e) = 1 := finrank_span_singleton he0
    rw [h] at h1
    omega
  obtain ⟨p, hpU, hpe, hfix'⟩ := CFSG.ClassicalGroups.PCoreSection.exists_fixed_mem_of_isPGroup hlin
    (T := L) hL (L := K' ∙ e) (P := U) hsp hU
    (fun t ht x hx => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      show (t : N ≃ₗ[K'] N) (c • e) ∈ _
      rw [map_smul, hefix t ht]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)) hne'
  refine ⟨p, hpU, hpe, fun g hg => ?_⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hfix' g hg)
  exact ⟨c, by rw [hc]; show (g : N ≃ₗ[K'] N) p = p + ((g : N ≃ₗ[K'] N) p - p); abel⟩

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem eichler_eq_of_coords {e p a b : N} (he : QN e = 0) (hp : QN p = 0)
    (hep : polar QN e p = 0) (ha : QN a = 0) (hb : QN b = 0) (hab : polar QN a b = 0)
    {α β γ δ : K'} (ha' : a = α • e + β • p) (hb' : b = γ • e + δ • p) :
    eichler QN a b = eichler QN e ((α * δ - β * γ) • p) := by
  have hc : polar QN e ((α * δ - β * γ) • p) = 0 := by rw [polar_smul_right_eq, hep, mul_zero]
  have hcQ : QN ((α * δ - β * γ) • p) = 0 := by rw [map_smul_eq_sq, hp, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply ha hab x, eichler_apply he hc x, hb, hcQ]
  subst ha' hb'
  simp only [polar_add_right, polar_smul_right_eq, zero_mul, add_zero]
  module

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem linearIndependent_pair_of_notMem_span {e p : N} (he0 : e ≠ 0) (hp : p ∉ K' ∙ e) :
    LinearIndependent K' ![e, p] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    apply hp
    have : p = (-(t⁻¹ * s)) • e := by
      calc p = t⁻¹ • (t • p) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = (-(t⁻¹ * s)) • e := by
          rw [eq_neg_of_add_eq_zero_right hst, smul_neg, smul_smul, neg_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
  subst ht
  rw [zero_smul, add_zero] at hst
  exact ⟨(smul_eq_zero.mp hst).resolve_right he0, rfl⟩

private theorem exists_fixed_pair (hnd : (polarBilin QN).Nondegenerate)
    {L : Subgroup ↥(elementaryGroup QN)} (hL : IsPGroup 2 L)
    (hLc : ∀ g ∈ L, ∀ g' ∈ L, g * g' = g' * g) {s₀ : ↥(elementaryGroup QN)} (hs₀L : s₀ ∈ L)
    (hs₀ : IsOrthA2 QN (s₀ : N ≃ₗ[K'] N)) :
    ∃ e p : N, QN e = 0 ∧ e ≠ 0 ∧ QN p = 0 ∧ polar QN e p = 0 ∧ LinearIndependent K' ![e, p] ∧
      (∀ g ∈ L, (g : N ≃ₗ[K'] N) e = e) ∧ (∀ g ∈ L, ∃ c : K', (g : N ≃ₗ[K'] N) p = p + c • e) ∧
      ∃ c : K', c ≠ 0 ∧ (s₀ : N ≃ₗ[K'] N) = eichler QN e (c • p) := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Submodule K' N, ℓ = commSpace (s₀ : N ≃ₗ[K'] N) := ⟨_, rfl⟩
  have hinv : ∀ g ∈ L, ∀ x ∈ ℓ, (g : N ≃ₗ[K'] N) x ∈ ℓ := by
    intro g hg x hx
    have hcomm : (g : N ≃ₗ[K'] N) * (s₀ : N ≃ₗ[K'] N) * (g : N ≃ₗ[K'] N)⁻¹ =
        (s₀ : N ≃ₗ[K'] N) := by
      have := congrArg Subtype.val (hLc g hg s₀ hs₀L)
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have h1 := commSpace_conj (g : N ≃ₗ[K'] N) (s₀ : N ≃ₗ[K'] N)
    rw [hcomm, ← hℓ] at h1
    rw [h1]
    exact Submodule.mem_map_of_mem hx
  have hℓ2 : finrank K' ℓ = 2 := by rw [hℓ]; exact hs₀.finrank_eq
  have hvan : ∀ x ∈ ℓ, QN x = 0 := by rw [hℓ]; exact hs₀.vanish
  obtain ⟨e, heℓ, he0, hLe, p, hpℓ, hpe, hLp⟩ := exists_fixed_pair_of_stable hL hℓ2 hinv
  have hli : LinearIndependent K' ![e, p] := linearIndependent_pair_of_notMem_span he0 hpe
  have hspan : Submodule.span K' ({e, p} : Set N) = ℓ :=
    span_pair_eq_of_finrank_eq_two hℓ2 heℓ hpℓ hli
  obtain ⟨a, b, hlab, ha, hb, hab, hs₀eq⟩ := hs₀.exists_eq_eichler hnd
  have hcs := (isOrthA2_eichler hnd ha hb hab hlab).2
  have hℓab : ℓ = Submodule.span K' {a, b} := by rw [hℓ, hs₀eq, hcs]
  have haℓ : a ∈ Submodule.span K' ({e, p} : Set N) := by
    rw [hspan, hℓab]; exact Submodule.subset_span (by simp)
  have hbℓ : b ∈ Submodule.span K' ({e, p} : Set N) := by
    rw [hspan, hℓab]; exact Submodule.subset_span (by simp)
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp haℓ
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.mp hbℓ
  have key := eichler_eq_of_coords (hvan e heℓ) (hvan p hpℓ)
    (polar_eq_zero_of_totallySingular hvan heℓ hpℓ) ha hb hab hαβ.symm hγδ.symm
  refine ⟨e, p, hvan e heℓ, he0, hvan p hpℓ, polar_eq_zero_of_totallySingular hvan heℓ hpℓ, hli,
    hLe, hLp, α * δ - β * γ, ?_, hs₀eq.trans key⟩
  intro hc0
  rw [hc0, zero_smul, eichler_zero_right] at key
  exact hs₀.ne_one (hs₀eq.trans key)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem pow_apply_of_apply_eq {h : N ≃ₗ[K'] N} {x : N} (hx : h x = x) (n : ℕ) :
    (h ^ n) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hx, ih]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem exists_mem_rootGroup_pow_eq {e : N} {s h : N ≃ₗ[K'] N}
    (hs : s ∈ rootGroup QN e) (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup QN) (hhe : h e = e)
    (n : ℕ) : ∃ t ∈ rootGroup QN e, (s * h) ^ n = t * h ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨t, ht, hn⟩ := ih
    have hconj := conj_mem_rootGroup (pow_mem hhO n) hs
    rw [pow_apply_of_apply_eq hhe n] at hconj
    refine ⟨t * (h ^ n * s * (h ^ n)⁻¹), mul_mem ht hconj, ?_⟩
    rw [pow_succ, hn]
    group

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem levi_apply_eq {e f p : N} (he : QN e = 0) (hef : polar QN e f = 1)
    (hpe : polar QN p e = 0) (hpf : polar QN p f = 0) {w : N} (hw : polar QN e w = 0)
    {h : N ≃ₗ[K'] N} (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup QN) (hhe : h e = e)
    (hhf : h f = f) {c : K'} (hgp : (eichler QN e w * h) p = p + c • e) : h p = p := by
  have hqe : polar QN (h p) e = 0 := by
    have := polar_map_of_mem hhO p e
    rwa [hhe, hpe] at this
  have hqf : polar QN (h p) f = 0 := by
    have := polar_map_of_mem hhO p f
    rwa [hhf, hpf] at this
  have h1 : eichler QN e w (h p) = h p - polar QN (h p) w • e := by
    rw [eichler_apply he hw, hqe]
    simp
  rw [LinearEquiv.mul_apply, h1] at hgp
  obtain ⟨t, ht⟩ : ∃ t, t = polar QN (h p) w := ⟨_, rfl⟩
  rw [← ht] at hgp
  have h2 : h p = p + (c + t) • e := by
    rw [add_smul, ← add_assoc, ← hgp]
    abel
  rw [h2, polar_add_left, polar_smul_left_eq, hpf, hef] at hqf
  have hct : c + t = 0 := by simpa using hqf
  rw [h2, hct, zero_smul, add_zero]

private theorem exists_eichler_mul_eichler {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) (hnd : (polarBilin QN).Nondegenerate)
    {g : ↥(elementaryGroup QN)} {k : ℕ} (hgk : g ^ 2 ^ k = 1)
    (hge : (g : N ≃ₗ[K'] N) e = e) {c : K'} (hgp : (g : N ≃ₗ[K'] N) p = p + c • e) :
    ∃ w y : N, polar QN e w = 0 ∧ polar QN e y = 0 ∧ polar QN f y = 0 ∧ polar QN p y = 0 ∧
      polar QN p' y = 0 ∧ (g : N ≃ₗ[K'] N) = eichler QN e w * eichler QN p y := by
  have hgO : (g : N ≃ₗ[K'] N) ∈ TauCeti.QuadraticMap.orthogonalGroup QN :=
    elementaryGroup_le_orthogonalGroup QN g.2
  have hef : polar QN e f ≠ 0 := by rw [hF.ef]; exact one_ne_zero
  obtain ⟨s, hs, h, hhO, hhe, hhf, hgsh⟩ :=
    exists_mem_rootGroup_mul_eq hF.e_sing hF.f_sing hef hgO hge
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hs
  have hpe : polar QN p e = 0 := by rw [polar_comm]; exact hF.ep
  have hpf : polar QN p f = 0 := by rw [polar_comm]; exact hF.fp
  have hhp : h p = p :=
    levi_apply_eq hF.e_sing hF.ef hpe hpf hw hhO hhe hhf (by rw [← hgsh]; exact hgp)
  have hgk' : (g : N ≃ₗ[K'] N) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hgk
    simpa using this
  obtain ⟨t, ht, htt⟩ := exists_mem_rootGroup_pow_eq hs hhO hhe (2 ^ k)
  rw [← hgsh, hgk'] at htt
  have hpow : h ^ 2 ^ k = 1 := by
    have hmem : h ^ 2 ^ k ∈ rootGroup QN e := by
      have : h ^ 2 ^ k = t⁻¹ := eq_inv_of_mul_eq_one_right htt.symm
      rw [this]
      exact inv_mem ht
    exact eq_one_of_mem_rootGroup_of_apply_eq hF.e_sing hef hmem (pow_apply_of_apply_eq hhf _)
  have hBp : IsPGroup 2 (Subgroup.zpowers h) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hhE : h ∈ elementaryGroup QN := by
    have : h = (eichler QN e w)⁻¹ * (g : N ≃ₗ[K'] N) := by rw [hgsh]; group
    rw [this]
    exact mul_mem (inv_mem (eichler_mem_elementaryGroup QN e w)) g.2
  let S : Subgroup (N ≃ₗ[K'] N) := MulAction.stabilizer _ e ⊓ MulAction.stabilizer _ f ⊓
    MulAction.stabilizer _ p
  have hhS : h ∈ S := ⟨⟨hhe, hhf⟩, hhp⟩
  have hBS : ∀ b ∈ Subgroup.zpowers h, b e = e ∧ b f = f ∧ b p = p := fun b hb => by
    have hbS := Subgroup.zpowers_le.mpr hhS hb
    exact ⟨hbS.1.1, hbS.1.2, hbS.2⟩
  have key := MinusThreeFrame.exists_eq_eichler_of_fixed hF hnd (B := Subgroup.zpowers h) hBp
    (Subgroup.zpowers_le.mpr hhO)
    (fun b hb => (elementaryGroup_le_omegaGroup hnd (Subgroup.zpowers_le.mpr hhE hb)).2)
    (fun b hb => (hBS b hb).1) (fun b hb => (hBS b hb).2.1) hF.p_sing hF.p'_sing hF.pp' hF.ep
    hF.fp hF.ep' hF.fp' (fun b hb => (hBS b hb).2.2)
  obtain ⟨y, hye, hyf, hyp, hyp', hhy⟩ := key h (Subgroup.mem_zpowers h)
  exact ⟨w, y, hw, hye, hyf, hyp, hyp', by rw [hgsh, hhy]⟩

end LineFixed

section Dim

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem finrank_le_add_of_forall (T : V →ₗ[K] V) {U C D : Submodule K V}
    (hC : ∀ u ∈ U, T u ∈ C) (hD : ∀ u ∈ U, T u = 0 → u ∈ D) :
    finrank K U ≤ finrank K C + finrank K D := by
  let T' : U →ₗ[K] C := (T.domRestrict U).codRestrict C fun u => hC u u.2
  have h1 := LinearMap.finrank_range_add_finrank_ker T'
  have h2 : finrank K (LinearMap.range T') ≤ finrank K C := Submodule.finrank_le _
  have h3 : finrank K (LinearMap.ker T') ≤ finrank K D := by
    let ι : LinearMap.ker T' →ₗ[K] D :=
      (U.subtype ∘ₗ (LinearMap.ker T').subtype).codRestrict D fun x => by
        have hx := x.2
        rw [LinearMap.mem_ker] at hx
        refine hD x.1 x.1.2 ?_
        exact congrArg Subtype.val hx
    refine LinearMap.finrank_le_finrank_of_injective (f := ι) fun x y hxy => ?_
    have h' : ((x : U) : V) = ((y : U) : V) := congrArg (fun z : D => (z : V)) hxy
    exact Subtype.ext (Subtype.ext h')
  omega

end Dim

section Anisotropic

variable {K' : Type} [Field K'] [CharP K' 2] {N : Type} [AddCommGroup N]
  [Module K' N] {QN : QuadraticForm K' N}

private theorem MinusThreeFrame.qf_ne_zero_of_perp {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) {y : N} (hye : polar QN e y = 0)
    (hyf : polar QN f y = 0) (hyp : polar QN p y = 0) (hyp' : polar QN p' y = 0) (hy0 : y ≠ 0) :
    QN y ≠ 0 := by
  intro hQ
  obtain ⟨c, hc⟩ := hF.eq_smul_of_polar_eq_zero (w := y) (w' := p)
    (by rw [polar_comm]; exact hye) (by rw [polar_comm]; exact hyf)
    (by rw [polar_comm]; exact hF.ep) (by rw [polar_comm]; exact hF.fp) hQ hF.p_sing hy0
    (by rw [polar_comm]; exact hyp)
  have h1 := hF.pp'
  rw [hc, polar_smul_left_eq, polar_comm QN y p', hyp', mul_zero] at h1
  exact zero_ne_one h1

end Anisotropic

section Rho

variable {K' : Type} [Field K'] [CharP K' 2] [Finite K'] {N : Type} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

private noncomputable abbrev axisSpace (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)) (a : N) :
    Submodule K V :=
  ⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)

private structure Ctx (Qf : QuadraticForm K V) (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V))
    (e f p p' u v : N) : Prop where
  hs : OmegaSetting QN Qf ρ
  htop : commutatorSpace ρ.range = ⊤
  hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0
  hK : 2 < Nat.card K'
  hF : MinusThreeFrame QN e f p p' u v
  h8 : finrank K V = 8

variable {e f p p' u v : N}

private theorem Ctx.fix_of_mem (c : Ctx Qf ρ e f p p' u v) {a w : N} (ha : QN a = 0)
    (ha0 : a ≠ 0) (haw : polar QN a w = 0) {z : V} (hz : z ∈ axisSpace ρ a) :
    rhoE ρ a w z = z :=
  (c.hs.forall_rhoE_apply_eq_iff_mem_iSup c.htop c.hfix c.hK c.hF c.h8 ha ha0 z).mpr hz w haw

private theorem Ctx.mem_of_fix (c : Ctx Qf ρ e f p p' u v) {a w : N} (ha : QN a = 0)
    (ha0 : a ≠ 0) (haw : polar QN a w = 0) (hw : QN w ≠ 0) {z : V} (hz : rhoE ρ a w z = z) :
    z ∈ axisSpace ρ a :=
  (c.hs.rhoE_apply_eq_iff_mem_iSup c.htop c.hfix c.hK c.hF c.h8 ha ha0 haw hw z).mp hz

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem movedSpace_le_axisSpace {a w : N} (haw : polar QN a w = 0) :
    movedSpace (rhoE ρ a w) ≤ axisSpace ρ a :=
  le_iSup₂_of_le (f := fun w (_ : polar QN a w = 0) => movedSpace (rhoE ρ a w)) w haw le_rfl

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
private theorem apply_mem_axisSpace {g : ↥(elementaryGroup QN)} {a : N}
    (hga : (g : N ≃ₗ[K'] N) a = a) {z : V} (hz : z ∈ axisSpace ρ a) : ρ g z ∈ axisSpace ρ a := by
  have h := OmegaSetting.map_iSup_movedSpace_rhoE (ρ := ρ) g a
  rw [hga] at h
  have := Submodule.mem_map_of_mem (f := (ρ g : V →ₗ[K] V)) hz
  rw [h] at this
  exact this

omit [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem Ctx.movedSpace_le_inf (c : Ctx Qf ρ e f p p' u v) :
    movedSpace (rhoE ρ e p) ≤ axisSpace ρ e ⊓ axisSpace ρ p :=
  le_inf (movedSpace_le_axisSpace c.hF.ep) (by
    rw [rhoE_comm c.hF.e_sing c.hF.p_sing c.hF.ep]
    exact movedSpace_le_axisSpace (by rw [polar_comm]; exact c.hF.ep))

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem rho_eq_rhoE_mul {g : ↥(elementaryGroup QN)} {a w b y : N}
    (hg : (g : N ≃ₗ[K'] N) = eichler QN a w * eichler QN b y) :
    ρ g = rhoE ρ a w * rhoE ρ b y := by
  have : g = ⟨eichler QN a w, eichler_mem_elementaryGroup QN a w⟩ *
      ⟨eichler QN b y, eichler_mem_elementaryGroup QN b y⟩ := Subtype.ext hg
  rw [this, map_mul]
  rfl

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem rho_eq_rhoE {g : ↥(elementaryGroup QN)} {a w : N}
    (hg : (g : N ≃ₗ[K'] N) = eichler QN a w) : ρ g = rhoE ρ a w := by
  have : g = ⟨eichler QN a w, eichler_mem_elementaryGroup QN a w⟩ := Subtype.ext hg
  rw [this]
  rfl

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem ne_zero_of_polar_eq_one' {a b : N} (h : polar QN a b = 1) : a ≠ 0 := by
  rintro rfl
  rw [polar_zero_left] at h
  exact zero_ne_one h

private theorem Ctx.apply_eq_of_mem_movedSpace (ctx : Ctx Qf ρ e f p p' u v) (he0 : e ≠ 0)
    (hp0 : p ≠ 0) {g : ↥(elementaryGroup QN)} {w y : N} (hw : polar QN e w = 0)
    (hy : polar QN p y = 0) (hg : (g : N ≃ₗ[K'] N) = eichler QN e w * eichler QN p y) {z : V}
    (hz : z ∈ movedSpace (rhoE ρ e p)) : ρ g z = z := by
  have hz' := ctx.movedSpace_le_inf hz
  rw [rho_eq_rhoE_mul hg, LinearEquiv.mul_apply, ctx.fix_of_mem ctx.hF.p_sing hp0 hy hz'.2,
    ctx.fix_of_mem ctx.hF.e_sing he0 hw hz'.1]

private theorem Ctx.eq_zero_of_hstar (ctx : Ctx Qf ρ e f p p' u v) (he0 : e ≠ 0) (hp0 : p ≠ 0)
    (hli : LinearIndependent K' ![e, p]) {L : Subgroup ↥(elementaryGroup QN)} {b₀ : V}
    (hb₀0 : b₀ ≠ 0) (hb₀ : b₀ ∈ movedSpace (rhoE ρ e p))
    (hLA : ∀ g ∈ L, ∀ z ∈ movedSpace (rhoE ρ e p), ρ g z = z)
    (hstar : ∀ g ∈ L, ∀ y : V, polar Qf b₀ y = 0 →
      (∀ g' ∈ L, ρ g' (ρ g y - y) = ρ g y - y) → ∃ c : K, ρ g y - y = c • b₀)
    {g : ↥(elementaryGroup QN)} (hg : g ∈ L) {w y : N} (hw : polar QN e w = 0)
    (hye : polar QN e y = 0) (hyf : polar QN f y = 0) (hyp : polar QN p y = 0)
    (hyp' : polar QN p' y = 0)
    (hdec : (g : N ≃ₗ[K'] N) = eichler QN e w * eichler QN p y) : y = 0 := by
  by_contra hy0
  have hQy : QN y ≠ 0 := ctx.hF.qf_ne_zero_of_perp hye hyf hyp hyp' hy0
  have hinf := ctx.hs.iSup_inf_iSup_eq_movedSpace ctx.htop ctx.hfix ctx.hK ctx.hF ctx.h8
  have hdim4 : finrank K (axisSpace ρ e) = 4 :=
    ctx.hs.finrank_iSup_movedSpace_rhoE_eq_four ctx.htop ctx.hfix ctx.hK ctx.hF ctx.h8
      ctx.hF.e_sing he0
  have hdim2 := ctx.hs.finrank_movedSpace_rhoE ctx.hF.e_sing ctx.hF.p_sing ctx.hF.ep hli
  let h : ↥(elementaryGroup QN) := ⟨eichler QN p y, eichler_mem_elementaryGroup QN p y⟩
  have hhe : (h : N ≃ₗ[K'] N) e = e := eichler_apply_of_polar_eq_zero ctx.hF.ep hye
  have hρh : ρ h = rhoE ρ p y := rfl
  have hstab : ∀ z ∈ axisSpace ρ e, rhoE ρ p y z ∈ axisSpace ρ e := fun z hz => by
    have := apply_mem_axisSpace (ρ := ρ) hhe hz
    rwa [hρh] at this
  have hgz : ∀ z ∈ axisSpace ρ e, ρ g z - z = rhoE ρ p y z - z := by
    intro z hz
    rw [rho_eq_rhoE_mul hdec, LinearEquiv.mul_apply,
      ctx.fix_of_mem ctx.hF.e_sing he0 hw (hstab z hz)]
  have hdiff : ∀ z ∈ axisSpace ρ e, ρ g z - z ∈ movedSpace (rhoE ρ e p) := by
    intro z hz
    rw [hgz z hz, ← hinf]
    exact ⟨Submodule.sub_mem _ (hstab z hz) hz,
      movedSpace_le_axisSpace hyp (sub_mem_movedSpace _ z)⟩
  have hb₀e : b₀ ∈ axisSpace ρ e := (ctx.movedSpace_le_inf hb₀).1
  have hpol : ∀ z ∈ axisSpace ρ e, polar Qf b₀ z = 0 := fun z hz =>
    polar_eq_zero_of_totallySingular (A := axisSpace ρ e)
      (fun x hx => ctx.hs.qf_eq_zero_of_mem_iSup_movedSpace_rhoE ctx.htop ctx.hfix ctx.hK ctx.hF
        ctx.h8 ctx.hF.e_sing he0 hx) hb₀e hz
  let T : V →ₗ[K] V := (rhoE ρ p y : V →ₗ[K] V) - 1
  have hT : ∀ z, T z = rhoE ρ p y z - z := fun z => by simp [T]
  have hC : ∀ z ∈ axisSpace ρ e, T z ∈ K ∙ b₀ := by
    intro z hz
    obtain ⟨c', hc'⟩ := hstar g hg z (hpol z hz)
      (fun g' hg' => hLA g' hg' _ (hdiff z hz))
    rw [hT, ← hgz z hz, hc']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b₀)
  have hD : ∀ z ∈ axisSpace ρ e, T z = 0 → z ∈ movedSpace (rhoE ρ e p) := by
    intro z hz hTz
    rw [hT, sub_eq_zero] at hTz
    rw [← hinf]
    exact ⟨hz, ctx.mem_of_fix ctx.hF.p_sing hp0 hyp hQy hTz⟩
  have hle := finrank_le_add_of_forall T hC hD
  rw [hdim2, finrank_span_singleton hb₀0] at hle
  omega

private theorem Ctx.natCard_le_of_le_rootGroup (ctx : Ctx Qf ρ e f p p' u v)
    (hnd : (polarBilin QN).Nondegenerate) (he0 : e ≠ 0) {L : Subgroup ↥(elementaryGroup QN)}
    {b₀ : V} (hb₀0 : b₀ ≠ 0) (hLR : ∀ g ∈ L, (g : N ≃ₗ[K'] N) ∈ rootGroup QN e)
    (hstar : ∀ g ∈ L, ∀ y : V, polar Qf b₀ y = 0 →
      (∀ g' ∈ L, ρ g' (ρ g y - y) = ρ g y - y) → ∃ c : K, ρ g y - y = c • b₀) :
    Nat.card L ≤ Nat.card K' := by
  by_contra hlt
  push Not at hlt
  have hY : L.map (elementaryGroup QN).subtype ≤ rootGroup QN e := by
    rintro _ ⟨g, hg, rfl⟩
    exact hLR g hg
  have hcard : Nat.card K' < Nat.card (L.map (elementaryGroup QN).subtype) := by
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  obtain ⟨w, hew, hQw, hmem⟩ := MinusThreeFrame.exists_eichler_mem_of_lt_natCard_of_point ctx.hF
    hnd ctx.hF.e_sing he0 hY hcard
  obtain ⟨g₁, hg₁, hg₁w⟩ := Subgroup.mem_map.mp hmem
  have hρg₁ : ρ g₁ = rhoE ρ e w := rho_eq_rhoE hg₁w
  have hdim4 : finrank K (axisSpace ρ e) = 4 :=
    ctx.hs.finrank_iSup_movedSpace_rhoE_eq_four ctx.htop ctx.hfix ctx.hK ctx.hF ctx.h8
      ctx.hF.e_sing he0
  let U := LinearMap.BilinForm.orthogonal (polarBilin Qf) (K ∙ b₀)
  have hU : finrank K U = 7 := by
    rw [finrank_orthogonal_polar ctx.hs.nd, ctx.h8, finrank_span_singleton hb₀0]
  let T : V →ₗ[K] V := (rhoE ρ e w : V →ₗ[K] V) - 1
  have hT : ∀ z, T z = rhoE ρ e w z - z := fun z => by simp [T]
  have hC : ∀ z ∈ U, T z ∈ K ∙ b₀ := by
    intro z hz
    have hpol : polar Qf b₀ z = 0 :=
      mem_orthogonal_iff_polar.mp hz b₀ (Submodule.mem_span_singleton_self b₀)
    have hmemW : rhoE ρ e w z - z ∈ axisSpace ρ e := by
      have h1 : rhoE ρ e w z - z ∈ movedSpace (rhoE ρ e w) := sub_mem_movedSpace _ z
      rwa [ctx.hs.movedSpace_rhoE_eq_iSup ctx.htop ctx.hfix ctx.hK ctx.hF ctx.h8 ctx.hF.e_sing
        he0 hew hQw] at h1
    have hfx : ∀ g' ∈ L, ρ g' (ρ g₁ z - z) = ρ g₁ z - z := by
      intro g' hg'
      obtain ⟨w', hw', hgw'⟩ := mem_rootGroup.mp (hLR g' hg')
      have hm : ρ g₁ z - z ∈ axisSpace ρ e := by rw [hρg₁]; exact hmemW
      rw [rho_eq_rhoE hgw'.symm]
      exact ctx.fix_of_mem ctx.hF.e_sing he0 hw' hm
    obtain ⟨c', hc'⟩ := hstar g₁ hg₁ z hpol hfx
    rw [hT, ← hρg₁, hc']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b₀)
  have hD : ∀ z ∈ U, T z = 0 → z ∈ axisSpace ρ e := fun z _ hz => by
    rw [hT, sub_eq_zero] at hz
    exact ctx.mem_of_fix ctx.hF.e_sing he0 hew hQw hz
  have hle := finrank_le_add_of_forall T hC hD
  rw [hU, hdim4, finrank_span_singleton hb₀0] at hle
  omega

end Rho

variable {K' : Type} [Field K'] [CharP K' 2] [Finite K'] {N : Type} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

theorem OmegaSetting.natCard_le_of_fixed_comm (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {L : Subgroup ↥(elementaryGroup QN)} (hL : IsPGroup 2 L)
    (hLc : ∀ g ∈ L, ∀ g' ∈ L, g * g' = g' * g) {s₀ : ↥(elementaryGroup QN)} (hs₀L : s₀ ∈ L)
    (hs₀ : IsOrthA2 QN (s₀ : N ≃ₗ[K'] N))
    {b₀ : V} (hb₀ : b₀ ≠ 0) (hb₀s : b₀ ∈ movedSpace (ρ s₀)) (_hLb : ∀ g ∈ L, ρ g b₀ = b₀)
    (hstar : ∀ g ∈ L, ∀ y : V, polar Qf b₀ y = 0 →
      (∀ g' ∈ L, ρ g' (ρ g y - y) = ρ g y - y) → ∃ c : K, ρ g y - y = c • b₀) :
    Nat.card L ≤ Nat.card K' := by
  obtain ⟨e₁, p₁, he, he0, hp, hep, hli, hLe, hLp, c₀, hc₀, hs₀eq⟩ :=
    exists_fixed_pair hs.ndN hL hLc hs₀L hs₀
  obtain ⟨f₁, p₁', u₁, v₁, hF'⟩ := MinusThreeFrame.exists_frame_of_flag hF hs.ndN he hp hep hli
  have ctx : Ctx Qf ρ e₁ f₁ p₁ p₁' u₁ v₁ := ⟨hs, htop, hfix, hK, hF', h8⟩
  have hp0 : p₁ ≠ 0 := ne_zero_of_polar_eq_one' hF'.pp'
  have hdec : ∀ g ∈ L, ∃ w y : N, polar QN e₁ w = 0 ∧ polar QN e₁ y = 0 ∧ polar QN f₁ y = 0 ∧
      polar QN p₁ y = 0 ∧ polar QN p₁' y = 0 ∧
      (g : N ≃ₗ[K'] N) = eichler QN e₁ w * eichler QN p₁ y := by
    intro g hg
    obtain ⟨k, hk⟩ := hL ⟨g, hg⟩
    obtain ⟨c, hc⟩ := hLp g hg
    exact exists_eichler_mul_eichler hF' hs.ndN (g := g) (k := k)
      (by simpa using congrArg Subtype.val hk) (hLe g hg) hc
  have hII := hs.caseII_of_six_lt_finrank htop hF' (by omega)
  have hpe' : polar QN p₁ e₁ = 0 := by rw [polar_comm]; exact hep
  have hpf' : polar QN p₁ f₁ = 0 := by rw [polar_comm]; exact hF'.fp
  have hax : movedSpace (ρ s₀) = movedSpace (rhoE ρ e₁ p₁) := by
    have h1 := hs.caseII_single_axis hfix hF' hII hF'.p_sing hp0 hpe' hpf' hc₀
    have h2 := hs.caseII_single_axis hfix hF' hII hF'.p_sing hp0 hpe' hpf'
      (one_ne_zero : (1 : K') ≠ 0)
    rw [one_smul] at h2
    rw [rho_eq_rhoE hs₀eq, h1, ← h2]
  have hb₀A : b₀ ∈ movedSpace (rhoE ρ e₁ p₁) := hax ▸ hb₀s
  have hLA : ∀ g ∈ L, ∀ z ∈ movedSpace (rhoE ρ e₁ p₁), ρ g z = z := by
    intro g hg z hz
    obtain ⟨w, y, hw, -, -, hyp, -, hdg⟩ := hdec g hg
    exact ctx.apply_eq_of_mem_movedSpace he0 hp0 hw hyp hdg hz
  have hLR : ∀ g ∈ L, (g : N ≃ₗ[K'] N) ∈ rootGroup QN e₁ := by
    intro g hg
    obtain ⟨w, y, hw, hye, hyf, hyp, hyp', hdg⟩ := hdec g hg
    have hy0 := ctx.eq_zero_of_hstar he0 hp0 hli hb₀ hb₀A hLA hstar hg hw hye hyf hyp hyp' hdg
    rw [hdg, hy0, eichler_zero_right, mul_one]
    exact eichler_mem_rootGroup hw
  exact ctx.natCard_le_of_le_rootGroup hs.ndN he0 hb₀ hLR hstar

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

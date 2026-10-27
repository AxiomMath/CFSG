module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Outer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Omega268
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Congr

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

theorem ModelB.congr (e : X ≃* Y) {ψ : MulAut X} (hM : ModelB X ψ) :
    ModelB Y (MulAut.congr e ψ) := by
  classical
  obtain ⟨hψ3, hψout, A, A₁, J, t, hAel, hAc, hψA, hA₁A, hA₁c, hJ, hAN, hJψ, hcm, hlay, ht1, ht2,
    htJ, htA, hψt⟩ := hM
  set ψ' : MulAut Y := MulAut.congr e ψ with hψ'
  set f : X →* Y := e.toMonoidHom with hfdef
  have hf : Function.Injective f := e.injective
  have hfe : ∀ x, f x = e x := fun x => rfl
  have hψ'pow : ∀ k : ℕ, ∀ x, (ψ' ^ k) (e x) = e ((ψ ^ k) x) := by
    intro k x
    rw [hψ', ← map_pow, MulAut.congr_apply]
    simp
  have hψ'e : ∀ x, ψ' (e x) = e (ψ x) := fun x => by
    simpa using hψ'pow 1 x
  have hmem : ∀ (K : Subgroup X) (x : X), e x ∈ K.map f ↔ x ∈ K := fun K x =>
    ⟨fun ⟨x', hx', h⟩ => hf h ▸ hx', fun hx => ⟨x, hx, rfl⟩⟩
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).2 hf, Subgroup.card_bot]
    norm_num
  refine ⟨?_, ?_, A.map f, A₁.map f, J.map f, e t, hAel.map f, ?_, ?_, Subgroup.map_mono hA₁A,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hψ', ← map_pow, hψ3, map_one]
  · rintro ⟨y, hy⟩
    apply hψout
    refine ⟨e.symm y, MulEquiv.ext fun x => e.injective ?_⟩
    have h1 := congrArg (fun α : MulAut Y => α (e x)) hy
    simp only [MulAut.conj_apply, hψ'e] at h1
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]
  · rw [Subgroup.card_map_of_injective hf, hAc]
  · rintro _ ⟨a, ha, rfl⟩
    rw [hfe, hψ'e, hψA a ha]
  · rw [Subgroup.card_map_of_injective hf, hA₁c]
  · have hc : (Subgroup.centralizer (A₁ : Set X)).map f =
        Subgroup.centralizer ((A₁.map f : Subgroup Y) : Set Y) := by
      rw [map_centralizer_eq f hf A₁, MonoidHom.range_eq_top.2 e.surjective, top_inf_eq]
    rw [← hc]
    refine glaPComponent_map Nat.prime_three f ?_ hJ
    rw [(MonoidHom.ker_eq_bot_iff f).2 hf, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  · rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 := Subgroup.mem_normalizer_iff.1 (hAN ha) x
    rw [hfe, ← map_inv, ← map_mul, ← map_mul, hmem, hmem]
    exact h1
  · ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hJx : ∀ z : X, z ∈ J ↔ ψ z ∈ J := fun z => by
      constructor
      · intro hz
        rw [← hJψ]
        exact ⟨z, hz, rfl⟩
      · intro hz
        rw [← hJψ] at hz
        obtain ⟨z', hz', h⟩ := hz
        rw [ψ.injective h] at hz'
        exact hz'
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
      change ψ' (e z) = e x at h
      rw [hψ'e] at h
      rw [hmem, ← e.injective h]
      exact (hJx z).1 hz
    · intro hx
      rw [hmem] at hx
      obtain ⟨z, hz, h⟩ := (hJψ.symm ▸ hx : x ∈ J.map ψ.toMonoidHom)
      refine ⟨e z, (hmem J z).2 hz, ?_⟩
      change ψ' (e z) = e x
      rw [hψ'e]
      exact congrArg e h
  · rintro _ ⟨a, ha, rfl⟩ k hk hj
    have h := hcm a ha k hk fun j hj' => by
      have h1 := hj (e j) ((hmem J j).2 hj')
      rw [hfe, hψ'pow, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul,
        ← map_glaPPrimeCoreOf Nat.prime_three f hker] at h1
      exact (hmem _ _).1 h1
    exact ⟨h.1, (hmem A₁ a).2 h.2⟩
  · have hfix : (fixSubgroup ψ).map f = fixSubgroup ψ' := by
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [hmem, mem_fixSubgroup, mem_fixSubgroup, hψ'e]
      exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
    rw [← hfix, ← Subgroup.map_inf_eq _ _ f hf, ← map_glaPLayer Nat.prime_three f hker]
    intro h
    exact hlay ((Subgroup.map_eq_bot_iff_of_injective _ hf).1 h)
  · intro h
    exact ht1 (e.injective (h.trans (map_one e).symm))
  · rw [← map_pow, ht2, map_one]
  · rintro _ ⟨j, hj, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (htJ hj)
    rw [Subgroup.mem_centralizer_singleton_iff, hfe, ← map_mul, ← map_mul, h1]
  · rintro _ ⟨a, ha, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (htA ha)
    rw [Subgroup.mem_centralizer_singleton_iff, hfe, ← map_mul, ← map_mul, h1]
  · rw [hψ'e, hψt]

end Congr

section Outer

variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_outer (H : P3Hyp q S B) (hZ : Subgroup.center ↥S = ⊥) {X : Type} [Group X]
    [Finite X] (φ : X →* Ω) (hφ : Function.Injective φ) (hφS : φ.range = S)
    (hZX : Subgroup.center X = ⊥) (hX : ∀ F : Subgroup X, IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 2)
    (hmodel : ∀ β : MulAut X, β ^ 3 = 1 → β ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ (g : X) (ψ : MulAut X), β = MulAut.conj g * ψ ∧ ModelB X ψ) :
    S267ConcA 3 S B := by
  haveI : S.Normal := H.normal
  obtain ⟨b₁, hb₁, β, hβout, hβφ⟩ := H.exists_outer_mem φ hφ hφS hZX hX
  have hb₁3 : b₁ ^ 3 = 1 := H.elem.2 b₁ hb₁
  have hβk : ∀ k : ℕ, ∀ x, φ ((β ^ k) x) = b₁ ^ k * φ x * (b₁ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hβφ, pow_succ]
      group
  have hβ3 : β ^ 3 = 1 := MulEquiv.ext fun x => hφ (by rw [hβk 3, hb₁3]; simp)
  obtain ⟨g, ψ, hβg, hM⟩ := hmodel β hβ3 hβout
  have hφmem : ∀ x, φ x ∈ S := fun x => hφS ▸ ⟨x, rfl⟩
  have hNS : ∀ b : Ω, b ∈ Subgroup.normalizer (S : Set Ω) := fun b => by
    rw [Subgroup.normalizer_eq_top_iff.2 H.normal]
    exact Subgroup.mem_top b
  set b' : Ω := (φ g)⁻¹ * b₁ with hb'
  have hb'φ : ∀ x, b' * φ x * b'⁻¹ = φ (ψ x) := by
    intro x
    have h1 := hβφ x
    rw [hβg, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    calc b' * φ x * b'⁻¹ = (φ g)⁻¹ * (b₁ * φ x * b₁⁻¹) * φ g := by rw [hb']; group
      _ = φ (ψ x) := by rw [← h1]; group
  have hψψψ : ∀ y, ψ (ψ (ψ y)) = y := fun y => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', hM.1, MulAut.one_apply]
  have hb'S : b' ^ 3 ∈ S := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hb', QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff (N := S) (φ g)).2 (hφmem g), inv_one,
      one_mul, ← QuotientGroup.mk_pow, hb₁3, QuotientGroup.mk_one]
  have hb'c : ∀ s ∈ S, s * b' ^ 3 = b' ^ 3 * s := by
    intro s hs
    rw [← hφS] at hs
    obtain ⟨x, rfl⟩ := hs
    have h3 : b' ^ 3 * φ x * (b' ^ 3)⁻¹ = φ x := by
      have e1 : b' ^ 3 * φ x * (b' ^ 3)⁻¹ = b' * (b' * (b' * φ x * b'⁻¹) * b'⁻¹) * b'⁻¹ := by
        rw [pow_three']
        simp only [mul_inv_rev, mul_assoc]
      rw [e1, hb'φ, hb'φ, hb'φ, hψψψ]
    calc φ x * b' ^ 3 = b' ^ 3 * φ x * (b' ^ 3)⁻¹ * b' ^ 3 := by rw [h3]
      _ = b' ^ 3 * φ x := by group
  have hb'3 : b' ^ 3 = 1 :=
    H.eq_one_of_mem_centMod hZ hb'S (S267.mem_centModSubgroup_of_commute (hNS _) hb'c)
  have hb'B₀ : ∀ b ∈ B ⊓ centModSubgroup 3 S, b' * b = b * b' := by
    intro b hb
    have h1 : Commute b (φ g) := H.comm_of_mem_centMod hb.2 (hφmem g)
    have h2 : Commute b b₁ :=
      congrArg Subtype.val (H.elem.1.is_comm.comm ⟨b, hb.1⟩ ⟨b₁, hb₁⟩)
    have hc : Commute b b' := by
      rw [hb']
      exact h1.inv_right.mul_right h2
    exact hc.eq.symm
  exact concA_of_modelB H hZ φ hφ hφS hb'3 hb'B₀ hb'φ hM

end Outer

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end

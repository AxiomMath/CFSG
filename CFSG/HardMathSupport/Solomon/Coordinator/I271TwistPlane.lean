module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL2Glue
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Lift
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistNorm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

section Plane

variable {X : Type} [Group X] [Finite X]

@[expose] def twFixer (K : Subgroup X) (x : X) : Subgroup X where
  carrier := {f | f ∈ Subgroup.normalizer (K : Set X) ∧
    f * x * f⁻¹ * x⁻¹ ∈ K ⊓ Subgroup.centralizer (K : Set X)}
  mul_mem' := by
    rintro f₁ f₂ ⟨hf₁N, hf₁⟩ ⟨hf₂N, hf₂⟩
    refine ⟨(Subgroup.normalizer (K : Set X)).mul_mem hf₁N hf₂N, ?_⟩
    have e : f₁ * f₂ * x * (f₁ * f₂)⁻¹ * x⁻¹ =
        (f₁ * (f₂ * x * f₂⁻¹ * x⁻¹) * f₁⁻¹) * (f₁ * x * f₁⁻¹ * x⁻¹) := by group
    rw [e]
    refine (K ⊓ Subgroup.centralizer (K : Set X)).mul_mem ?_ hf₁
    exact ⟨(Subgroup.mem_normalizer_iff.1 hf₁N _).1 hf₂.1, i224_conj_mem_centralizer hf₁N hf₂.2⟩
  one_mem' := ⟨Subgroup.one_mem _, by simpa using Subgroup.one_mem (K ⊓ Subgroup.centralizer (K : Set X))⟩
  inv_mem' := by
    rintro f ⟨hfN, hf⟩
    refine ⟨(Subgroup.normalizer (K : Set X)).inv_mem hfN, ?_⟩
    have e : f⁻¹ * x * f⁻¹⁻¹ * x⁻¹ = f⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * f := by group
    rw [e]
    have hinv : (f * x * f⁻¹ * x⁻¹)⁻¹ ∈ K ⊓ Subgroup.centralizer (K : Set X) :=
      (K ⊓ Subgroup.centralizer (K : Set X)).inv_mem hf
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (K : Set X)).inv_mem hfN) _).1
        hinv.1
      simpa using this
    · have := i224_conj_mem_centralizer ((Subgroup.normalizer (K : Set X)).inv_mem hfN) hinv.2
      simpa using this

theorem mem_i224Tw_of_fixer {K F : Subgroup X} {x : X} (hx : x ∈ K) (hF : F ≤ twFixer K x) :
    x ∈ i224Tw K F := ⟨hx, fun _ hf => (hF hf).2⟩

theorem hgen_of_plane {K B : Subgroup X} (hBel : IsElemAbelian 3 B) (hperf : commutator ↥K = ⊤)
    (h9 : autOrderIn B K = 9) {S : Type*} [Group S] (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    (hplane : ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 9 →
      Subgroup.closure {s : S | ∃ ε ∈ E, ε ≠ 1 ∧ ε s = s} = ⊤) :
    K ≤ ⨆ (F : Subgroup X)
      (_ : F ≤ B ⊓ Subgroup.normalizer (K : Set X) ∧
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) ≤ 3 * Nat.card F), i224Tw K F := by
  classical
  set N : Subgroup X := Subgroup.normalizer (K : Set X) with hN
  set A : Subgroup X := B ⊓ N with hA
  set C : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X) with hC
  have hAB : A ≤ B := inf_le_left
  have hAN : A ≤ N := inf_le_right
  have hCN : Subgroup.centralizer (K : Set X) ≤ N := Subgroup.centralizer_le_normalizer _
  have hCA : C ≤ A := inf_le_inf_left _ hCN
  have hAel : IsElemAbelian 3 A := CFSG.Open.IsElemAbelian.mono hBel hAB
  set θ := i271Act K e with hθ
  set E : Subgroup (MulAut S) := (A.subgroupOf N).map θ with hE
  have hEel : IsElemAbelian 3 E :=
    CFSG.SectionRank.isElemAbelian_map (i271_isElemAbelian_subgroupOf N hAel) θ
  have hEcard : Nat.card E = autOrderIn B K := by
    rw [hE, ← Subgroup.relIndex_ker, hθ, ker_i271Act hperf e,
      Subgroup.relIndex_subgroupOf hAN]
    rfl
  have hE9 : Nat.card E = 9 := hEcard.trans h9
  have hAC : Nat.card A = 9 * Nat.card C := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (K : Set X)) (K := A)
    have hinf : Subgroup.centralizer (K : Set X) ⊓ A = C := by
      ext x
      constructor
      · rintro ⟨hx1, hx2, hx3⟩
        exact ⟨hx2, hx1⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx2, hx1, hCN hx2⟩
    rw [hinf] at h
    have h' : autOrderIn B K = (Subgroup.centralizer (K : Set X)).relIndex A := rfl
    rw [← h', h9] at h
    exact h.symm
  have hclos := hplane E hEel hE9
  set H : Subgroup X := ⨆ (F : Subgroup X)
      (_ : F ≤ A ∧ Nat.card A ≤ 3 * Nat.card F), i224Tw K F with hH
  have hfix : ∀ s ∈ {s : S | ∃ ε ∈ E, ε ≠ 1 ∧ ε s = s},
      ∃ x : ↥K, e (x : ↥K ⧸ Subgroup.center ↥K) = s ∧ (x : X) ∈ H := by
    rintro s ⟨ε, hεE, hε1, hεs⟩
    obtain ⟨n, hn, rfl⟩ := hεE
    obtain ⟨q, rfl⟩ := e.surjective s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hbA : (n : X) ∈ A := Subgroup.mem_subgroupOf.1 hn
    have hθx : θ n (e (x : ↥K ⧸ Subgroup.center ↥K)) =
        e ((⟨(n : X) * x * (n : X)⁻¹, (Subgroup.mem_normalizer_iff.1 n.2 x).1 x.2⟩ : ↥K) :
          ↥K ⧸ Subgroup.center ↥K) := by
      show (MulAut.congr e) ((autCenterQuot ↥K) (K.normalizerMonoidHom n)) (e _) = _
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rfl
    have hcen : ((⟨(n : X) * x * (n : X)⁻¹, (Subgroup.mem_normalizer_iff.1 n.2 x).1 x.2⟩ : ↥K) :
        ↥K ⧸ Subgroup.center ↥K) = x := by
      apply e.injective
      rw [← hθx]
      exact hεs
    have hz := QuotientGroup.eq.1 hcen
    refine ⟨x, rfl, ?_⟩
    set b : X := (n : X) with hb
    have hbC : b ∉ C := by
      intro hbC
      apply hε1
      have hker : n ∈ θ.ker := by
        rw [hθ, ker_i271Act hperf e, Subgroup.mem_subgroupOf]
        exact hbC.2
      exact MonoidHom.mem_ker.1 hker
    have hFA : C ⊔ Subgroup.zpowers b ≤ A :=
      sup_le hCA ((Subgroup.zpowers_le).2 hbA)
    have hFC : C ⊔ Subgroup.zpowers b ≠ C := by
      intro h
      apply hbC
      rw [← h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    have hrk := pRank_sub_one_le_of_card hAel le_sup_left hFA hFC hAC
    have hFel : IsElemAbelian 3 (C ⊔ Subgroup.zpowers b) := CFSG.Open.IsElemAbelian.mono hAel hFA
    have hFcard : Nat.card A ≤ 3 * Nat.card ↥(C ⊔ Subgroup.zpowers b) :=
      (i224_card_le_iff Nat.prime_three hAel hFel).1 hrk
    have hxfix : C ⊔ Subgroup.zpowers b ≤ twFixer K (x : X) := by
      refine sup_le (fun c hc => ?_) ((Subgroup.zpowers_le).2 ?_)
      · refine ⟨hCN hc.2, ?_⟩
        have h1 := Subgroup.mem_centralizer_iff.1 hc.2 (x : X) x.2
        have : (c : X) * x * c⁻¹ * (x : X)⁻¹ = 1 := by
          calc c * (x : X) * c⁻¹ * (x : X)⁻¹ = ((x : X) * c) * c⁻¹ * (x : X)⁻¹ := by rw [h1]
            _ = 1 := by group
        rw [this]
        exact Subgroup.one_mem _
      · refine ⟨hAN hbA, ?_⟩
        set y : ↥K := ⟨(n : X) * x * (n : X)⁻¹, (Subgroup.mem_normalizer_iff.1 n.2 x).1 x.2⟩
          with hy
        have hw := Subgroup.mem_center_iff.1 hz x
        have hwinv := Subgroup.mem_center_iff.1 ((Subgroup.center ↥K).inv_mem hz) x
        have hyx : y * x⁻¹ ∈ Subgroup.center ↥K := by
          have e1 : y * x⁻¹ = (y⁻¹ * x)⁻¹ := by
            calc y * x⁻¹ = x * (x⁻¹ * y) * x⁻¹ := by group
              _ = x * (y⁻¹ * x)⁻¹ * x⁻¹ := by group
              _ = (y⁻¹ * x)⁻¹ * x * x⁻¹ := by rw [hwinv]
              _ = (y⁻¹ * x)⁻¹ := by group
          rw [e1]
          exact (Subgroup.center ↥K).inv_mem hz
        have e2 : b * (x : X) * b⁻¹ * (x : X)⁻¹ = ((y * x⁻¹ : ↥K) : X) := by
          simp [hy, hb]
        rw [e2]
        refine ⟨(y * x⁻¹).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
        have := Subgroup.mem_center_iff.1 hyx ⟨h, hh⟩
        exact congrArg Subtype.val this
    have hxT : (x : X) ∈ i224Tw K (C ⊔ Subgroup.zpowers b) := mem_i224Tw_of_fixer x.2 hxfix
    exact Subgroup.mem_iSup_of_mem (C ⊔ Subgroup.zpowers b)
      (Subgroup.mem_iSup_of_mem ⟨hFA, hFcard⟩ hxT)
  set H' : Subgroup ↥K := H.subgroupOf K with hH'
  have hW : ∀ g : ↥K, ∃ w ∈ H', w⁻¹ * g ∈ Subgroup.center ↥K := by
    intro g
    have hmem : e (g : ↥K ⧸ Subgroup.center ↥K) ∈
        Subgroup.closure {s : S | ∃ ε ∈ E, ε ≠ 1 ∧ ε s = s} := by
      rw [hclos]; exact Subgroup.mem_top _
    have hle : Subgroup.closure {s : S | ∃ ε ∈ E, ε ≠ 1 ∧ ε s = s} ≤
        (H'.map (QuotientGroup.mk' (Subgroup.center ↥K))).map e.toMonoidHom := by
      rw [Subgroup.closure_le]
      intro s hs
      obtain ⟨x, rfl, hxH⟩ := hfix s hs
      exact ⟨(x : ↥K ⧸ Subgroup.center ↥K), ⟨x, Subgroup.mem_subgroupOf.2 hxH, rfl⟩, rfl⟩
    obtain ⟨q, ⟨w, hw, rfl⟩, hq⟩ := hle hmem
    refine ⟨w, hw, ?_⟩
    have := e.injective hq
    exact QuotientGroup.eq.1 this
  have hH'top : H' = ⊤ := GL83.PiGen.eq_top_of_forall_exists_mul_mem_center hperf hW
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ H' := by rw [hH'top]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 this

end Plane

end CFSG.HardMathSupport.Solomon.Coordinator

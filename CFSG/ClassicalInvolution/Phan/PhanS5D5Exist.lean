module

public import CFSG.ClassicalInvolution.Phan.PhanS5D4CW

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.D

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] (M : Model K)

@[expose] def betaVec (a b : Vec K) : Vec K :=
  b - (bf M b (tauV M a) / her M a a) • a - (bf M b a / her M a a) • tauV M a

structure EFW (a b e f w : Vec K) : Prop where
  hyp : HypTriple M a e f w
  e_b : bf M e b = 0
  f_b : bf M f b = 0
  w_b : bf M w b = 0

variable {M}

theorem finrank_span_singleton_le (v : Vec K) :
    Module.finrank K (Submodule.span K ({v} : Set (Vec K))) ≤ 1 := by
  by_cases hv : v = 0
  · have h0 : Submodule.span K ({v} : Set (Vec K)) = ⊥ := by
      rw [hv]
      exact Submodule.span_zero_singleton K
    rw [h0, finrank_bot]
    omega
  · rw [finrank_span_singleton hv]

theorem eq_smul_beta_of_mem_span {a b v : Vec K} (ha : IsFF M a)
    (hv : v ∈ Submodule.span K ({a, tauV M a, b} : Set (Vec K))) (h1 : bf M v a = 0)
    (h2 : bf M v (tauV M a) = 0) : ∃ u : K, v = u • betaVec M a b := by
  obtain ⟨s, t, u, rfl⟩ := Submodule.mem_span_triple.mp hv
  have hh : her M a a ≠ 0 := ha.2
  have haa : bf M a a = 0 := ha.1
  have e1 : bf M (tauV M a) a = her M a a := by rw [bf_tauV_left, tau_her_self]
  have e2 : bf M a (tauV M a) = her M a a := rfl
  have e3 : bf M (tauV M a) (tauV M a) = 0 := by rw [bf_tauV, haa, map_zero]
  simp only [bf_add_left, bf_smul_left, haa, e1, e2, e3, mul_zero, zero_add, add_zero] at h1 h2
  refine ⟨u, ?_⟩
  have hs : s = -(u * bf M b (tauV M a) / her M a a) := by
    field_simp
    linear_combination h2
  have ht : t = -(u * bf M b a / her M a a) := by
    field_simp
    linear_combination h1
  rw [betaVec, hs, ht]
  module

theorem mem_orthSpan_three {x y z v : Vec K} :
    v ∈ orthSpan M ({x, y, z} : Set (Vec K)) ↔
      bf M x v = 0 ∧ bf M y v = 0 ∧ bf M z v = 0 := by
  rw [mem_orthSpan]
  simp

theorem mem_orthSpan_four {x y z t v : Vec K} :
    v ∈ orthSpan M ({x, y, z, t} : Set (Vec K)) ↔
      bf M x v = 0 ∧ bf M y v = 0 ∧ bf M z v = 0 ∧ bf M t v = 0 := by
  rw [mem_orthSpan]
  simp

theorem mem_orthSpan_five {x y z t r v : Vec K} :
    v ∈ orthSpan M ({x, y, z, t, r} : Set (Vec K)) ↔
      bf M x v = 0 ∧ bf M y v = 0 ∧ bf M z v = 0 ∧ bf M t v = 0 ∧ bf M r v = 0 := by
  rw [mem_orthSpan]
  simp

theorem exists_partner {e g : Vec K} (he : bf M e e = 0) (hd : bf M e g ≠ 0) :
    ∃ s t : K, bf M (s • g + t • e) (s • g + t • e) = 0 ∧ bf M e (s • g + t • e) = 1 := by
  have h2 := M.two_ne
  refine ⟨(bf M e g)⁻¹, -(bf M g g / (2 * (bf M e g) ^ 2)), ?_, ?_⟩
  · simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, he, bf_comm M g e]
    field_simp
    ring
  · simp only [bf_add_right, bf_smul_right, he]
    field_simp
    ring

theorem bf_decomp (w z e f : Vec K) :
    bf M w z = bf M w (z + (-(bf M z f)) • e + (-(bf M z e)) • f) + bf M z f * bf M w e +
      bf M z e * bf M w f := by
  simp only [bf_add_right, bf_smul_right]
  ring

theorem exists_efw [Finite K] {a : Vec K} (ha : IsFF M a) (b : Vec K) :
    ∃ e f w : Vec K, EFW M a b e f w := by
  classical
  have haa : bf M a a = 0 := ha.1
  obtain ⟨g, hg⟩ : ∃ g : Vec K, betaVec M a b = 0 ∨ bf M (betaVec M a b) g ≠ 0 := by
    by_cases h : betaVec M a b = 0
    · exact ⟨0, Or.inl h⟩
    · have h' : ¬ ∀ y, bf M (betaVec M a b) y = 0 := fun h' => h (eq_zero_of_bf_eq_zero M h')
      obtain ⟨y, hy⟩ := not_forall.mp h'
      exact ⟨y, Or.inr hy⟩
  have hZ₁dim : 3 ≤ Module.finrank K (orthSpan M ({a, tauV M a, b, g} : Set (Vec K))) := by
    have h1 := finrank_orthSpan_ge M ({a, tauV M a, b, g} : Finset (Vec K))
    have h2 : ({a, tauV M a, b, g} : Finset (Vec K)).card ≤ 4 := Finset.card_le_four
    have hcoe : (({a, tauV M a, b, g} : Finset (Vec K)) : Set (Vec K)) =
        {a, tauV M a, b, g} := by simp
    rw [hcoe] at h1
    omega
  have hZ₁T : ∀ v ∈ orthSpan M ({a, tauV M a, b, g} : Set (Vec K)),
      v ∈ Submodule.span K ({a, tauV M a, b} : Set (Vec K)) → v = 0 := by
    intro v hv hvT
    obtain ⟨hv1, hv2, -, hv4⟩ := mem_orthSpan_four.mp hv
    obtain ⟨u, rfl⟩ := eq_smul_beta_of_mem_span ha hvT (by rw [bf_comm]; exact hv1)
      (by rw [bf_comm]; exact hv2)
    rcases hg with h0 | hne
    · rw [h0, smul_zero]
    · rw [bf_smul_right, bf_comm M g] at hv4
      have hu : u = 0 := (mul_eq_zero.mp (by simpa [bf_comm M g] using hv4)).resolve_right hne
      rw [hu, zero_smul]
  obtain ⟨zf, hzf⟩ := exists_linearIndependent_of_le_finrank (R := K)
    (M := orthSpan M ({a, tauV M a, b, g} : Set (Vec K))) (n := 3) hZ₁dim
  have hz_ind : LinearIndependent K (fun i => (zf i : Vec K)) :=
    hzf.map' (Submodule.subtype _) (Submodule.ker_subtype _)
  obtain ⟨x, hx0, hxs⟩ := exists_singular_comb M (fun i => (zf i : Vec K))
  have he_mem : (∑ i, x i • (zf i : Vec K)) ∈ orthSpan M ({a, tauV M a, b, g} : Set (Vec K)) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (zf i).2
  have he_ne : (∑ i, x i • (zf i : Vec K)) ≠ 0 := fun h0 =>
    hx0 (funext fun i => Fintype.linearIndependent_iff.mp hz_ind x h0 i)
  generalize (∑ i, x i • (zf i : Vec K)) = e at he_mem he_ne hxs
  have he_T : e ∉ Submodule.span K ({a, tauV M a, b} : Set (Vec K)) := fun hT =>
    he_ne (hZ₁T e he_mem hT)
  obtain ⟨he1, he2, he3, -⟩ := mem_orthSpan_four.mp he_mem
  obtain ⟨g', hg'Z, hg'⟩ : ∃ g' ∈ orthSpan M ({a, tauV M a, b} : Set (Vec K)), bf M e g' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he_T (mem_span_of_forall_orth M hcon)
  have heZ : e ∈ orthSpan M ({a, tauV M a, b} : Set (Vec K)) :=
    mem_orthSpan_three.mpr ⟨he1, he2, he3⟩
  obtain ⟨s, t, hff, hef⟩ := exists_partner hxs hg'
  have hfZ : s • g' + t • e ∈ orthSpan M ({a, tauV M a, b} : Set (Vec K)) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hg'Z) (Submodule.smul_mem _ _ heZ)
  generalize s • g' + t • e = f at hfZ hff hef
  obtain ⟨hf1, hf2, hf3⟩ := mem_orthSpan_three.mp hfZ
  have hee : bf M e e = 0 := hxs
  have hef' : bf M f e = 1 := by rw [bf_comm, hef]
  have hae : bf M a e = 0 := he1
  have hsae : bf M (tauV M a) e = 0 := he2
  have hbe : bf M b e = 0 := he3
  have hZ₀dim : 2 ≤ Module.finrank K (orthSpan M ({a, tauV M a, b, e, f} : Set (Vec K))) := by
    have h1 := finrank_orthSpan_ge M ({a, tauV M a, b, e, f} : Finset (Vec K))
    have h2 : ({a, tauV M a, b, e, f} : Finset (Vec K)).card ≤ 5 := Finset.card_le_five
    have hcoe : (({a, tauV M a, b, e, f} : Finset (Vec K)) : Set (Vec K)) =
        {a, tauV M a, b, e, f} := by simp
    rw [hcoe] at h1
    omega
  obtain ⟨w, hwZ₀, hww⟩ : ∃ w ∈ orthSpan M ({a, tauV M a, b, e, f} : Set (Vec K)),
      bf M w w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : orthSpan M ({a, tauV M a, b, e, f} : Set (Vec K)) ≤
        Submodule.span K ({betaVec M a b} : Set (Vec K)) := by
      intro w hw
      obtain ⟨hwa, hwsa, hwb, hwe, hwf⟩ := mem_orthSpan_five.mp hw
      have hwT : w ∈ Submodule.span K ({a, tauV M a, b} : Set (Vec K)) := by
        refine mem_span_of_forall_orth M fun z hz => ?_
        obtain ⟨hza, hzsa, hzb⟩ := mem_orthSpan_three.mp hz
        obtain ⟨z₀, hz₀def⟩ : ∃ z₀ : Vec K,
            z₀ = z + (-(bf M z f)) • e + (-(bf M z e)) • f := ⟨_, rfl⟩
        have hz₀ : z₀ ∈ orthSpan M ({a, tauV M a, b, e, f} : Set (Vec K)) := by
          rw [hz₀def, mem_orthSpan_five]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [bf_add_right, bf_smul_right]
          · rw [hza, hae, hf1]; ring
          · rw [hzsa, hsae, hf2]; ring
          · rw [hzb, hbe, hf3]; ring
          · rw [hee, hef, bf_comm M e z]; ring
          · rw [hef', hff, bf_comm M f z]; ring
        have hsing : bf M w z₀ = 0 := by
          have h1 := hcon _ (Submodule.add_mem _ hw hz₀)
          have h2 := hcon w hw
          have h3 := hcon z₀ hz₀
          have hsym := bf_comm M w z₀
          rw [bf_add_left, bf_add_right, bf_add_right] at h1
          have h4 : (2 : K) * bf M w z₀ = 0 := by linear_combination h1 - h2 - h3 + hsym
          exact (mul_eq_zero.mp h4).resolve_left M.two_ne
        have hdec := bf_decomp (M := M) w z e f
        rw [← hz₀def, hsing, bf_comm M w e, bf_comm M w f, hwe, hwf] at hdec
        simpa using hdec
      obtain ⟨u, rfl⟩ := eq_smul_beta_of_mem_span ha hwT (by rw [bf_comm]; exact hwa)
        (by rw [bf_comm]; exact hwsa)
      exact Submodule.mem_span_singleton.mpr ⟨u, rfl⟩
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_span_singleton_le (betaVec M a b)
    omega
  obtain ⟨hwa, hwsa, hwb, hwe, hwf⟩ := mem_orthSpan_five.mp hwZ₀
  exact ⟨e, f, w, ⟨⟨by rw [bf_comm]; exact hae, by rw [bf_comm]; exact hsae,
    by rw [bf_comm]; exact hf1, by rw [bf_comm]; exact hf2, by rw [bf_comm]; exact hwa,
    by rw [bf_comm]; exact hwsa, hxs, hff, hef, by rw [bf_comm]; exact hwe,
    by rw [bf_comm]; exact hwf, hww⟩, by rw [bf_comm]; exact hbe,
    by rw [bf_comm]; exact hf3, by rw [bf_comm]; exact hwb⟩⟩

end CFSG.ClassicalInvolution.PhanB3.S.Std.D

module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3LSound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Codes

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof (sGen sGen_zero sGen_one sGen_two sGen_three
  sGen_four sGen_five)

variable {Γ : Type} [Group Γ] {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f13_orderOf_eq_two_iff {x : Γ} : orderOf x = 2 ↔ x ≠ 1 ∧ x * x = 1 := by
  rw [orderOf_eq_prime_iff, pow_two]
  exact and_comm

theorem f13_coe_sup {A Y : Subgroup Γ}
    (h : {g | ∃ a ∈ (A : Set Γ), ∃ y ∈ (Y : Set Γ), a * y = g} =
      {g | ∃ y ∈ (Y : Set Γ), ∃ a ∈ (A : Set Γ), y * a = g}) :
    ((A ⊔ Y : Subgroup Γ) : Set Γ) = {g | ∃ a ∈ (A : Set Γ), ∃ y ∈ (Y : Set Γ), a * y = g} := by
  let K : Subgroup Γ :=
    { carrier := {g | ∃ a ∈ (A : Set Γ), ∃ y ∈ (Y : Set Γ), a * y = g}
      mul_mem' := by
        rintro _ _ ⟨a, ha, y, hy, rfl⟩ ⟨a', ha', y', hy', rfl⟩
        have hya : y * a' ∈ {g | ∃ y ∈ (Y : Set Γ), ∃ a ∈ (A : Set Γ), y * a = g} :=
          ⟨y, hy, a', ha', rfl⟩
        rw [← h] at hya
        obtain ⟨a'', ha'', y'', hy'', he⟩ := hya
        refine ⟨a * a'', A.mul_mem ha ha'', y'' * y', Y.mul_mem hy'' hy', ?_⟩
        rw [← mul_assoc, mul_assoc a, he]
        simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, Y.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, y, hy, rfl⟩
        have hi : y⁻¹ * a⁻¹ ∈ {g | ∃ y ∈ (Y : Set Γ), ∃ a ∈ (A : Set Γ), y * a = g} :=
          ⟨y⁻¹, Y.inv_mem hy, a⁻¹, A.inv_mem ha, rfl⟩
        rw [← h] at hi
        rw [mul_inv_rev]
        exact hi }
  apply Set.Subset.antisymm
  · have hle : A ⊔ Y ≤ K :=
      sup_le (fun a ha => ⟨a, ha, 1, Y.one_mem, mul_one a⟩)
        (fun y hy => ⟨1, A.one_mem, y, hy, one_mul y⟩)
    exact fun x hx => hle hx
  · rintro _ ⟨a, ha, y, hy, rfl⟩
    exact (A ⊔ Y).mul_mem (mem_sup_left ha) (mem_sup_right hy)

theorem f13_conjClass_eq_of_mem {T : Subgroup Γ} {x y : Γ} (hy : y ∈ conjClass T x) :
    conjClass T y = conjClass T x := by
  obtain ⟨t, ht, hty⟩ := hy
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s * t, T.mul_mem hs ht, ?_⟩
    rw [hty]
    group
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s * t⁻¹, T.mul_mem hs (T.inv_mem ht), ?_⟩
    rw [hty]
    group

theorem f13_setOf_eq_map (l : List ℕ) :
    {x | ∃ g ∈ l, elt g = x} = {x | x ∈ l.map elt} := by
  ext x
  simp only [Set.mem_setOf_eq, List.mem_map]

theorem f13_setOf_one (u : Γ) : {x | x ∈ [u]} = ({u} : Set Γ) := by
  ext x
  simp

theorem f13_setOf_three (u v w : Γ) : {x | x ∈ [u, v, w]} = ({u, v, w} : Set Γ) := by
  ext x
  simp

theorem f13_setOf_five (u v w s t : Γ) :
    {x | x ∈ [u, v, w, s, t]} = ({u, v, w, s, t} : Set Γ) := by
  ext x
  simp

theorem f13_setOf_six (u v w s t r : Γ) :
    {x | x ∈ [u, v, w, s, t, r]} = ({u, v, w, s, t, r} : Set Γ) := by
  ext x
  simp

theorem f13_mulE_lt (P x y : ℕ) : mulE P x y < 128 := atR_lt _ _

section Tables

variable (hR : RealT elt P C V Q)
include hR

theorem f13_cenE {X : ℕ} {T : Subgroup Γ} (hX : mset elt X = (T : Set Γ)) {y : ℕ}
    (hy : y < 128) : mset elt (cenE P C X y) = (centEl T (elt y) : Set Γ) := by
  rw [cenE_mset hR X hy, hX]
  ext x
  simp only [centEl, Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
    Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, Set.mem_setOf_eq]
  exact and_congr Iff.rfl eq_comm

theorem f13_involM {X : ℕ} {T : Subgroup Γ} (hX : mset elt X = (T : Set Γ)) :
    mset elt (involM Q X) = invols T := by
  rw [involM_mset hR X, hX]
  ext x
  simp only [invols, Set.mem_setOf_eq, SetLike.mem_coe, f13_orderOf_eq_two_iff]

theorem f13_clsE {X : ℕ} {T : Subgroup Γ} (hX : mset elt X = (T : Set Γ)) {y : ℕ}
    (hy : y < 128) : mset elt (clsE P C V X y) = conjClass T (elt y) := by
  rw [clsE_mset hR X hy, hX]
  ext w
  simp only [conjClass, Set.mem_setOf_eq, SetLike.mem_coe]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩

theorem f13_right {X : ℕ} {T : Set Γ} (hX : mset elt X = T) {y : ℕ} (hy : y < 128) :
    mset elt (imgR (rowT C y) X) = {w | ∃ c ∈ T, w = c * elt y} := by
  rw [mset_imgR_right hR hy, hX]
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩⟩

theorem f13_supCK {S Ss : ℕ} {TS TSs : Subgroup Γ} (hS : mset elt S = (TS : Set Γ))
    (hSs : mset elt Ss = (TSs : Set Γ)) {y : ℕ} (hy : y < 128) {gs : List ℕ}
    (hgs : ∀ g ∈ gs, g < 128) {R : ℕ} (h : supCK P C S Ss y gs R = true) :
    centEl TSs (elt y) = centEl TS (elt y) ⊔ closure {x | ∃ g ∈ gs, elt g = x} := by
  simp only [supCK, bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hc, hp, he⟩ := h
  have hp' := permB_spec hR hp
  rw [f13_cenE hR hS hy, closK_closure hR hgs hc] at hp'
  apply SetLike.coe_injective
  rw [← f13_cenE hR hSs hy, he, prodM_mset hR, f13_cenE hR hS hy, closK_closure hR hgs hc,
    f13_coe_sup hp']

end Tables

variable [Finite Γ] {fr : Frame Γ}

theorem f13_gens (hg : ∀ s < 6, elt (s + 1) = sGen fr s) :
    elt 1 = fr.a₁ ∧ elt 2 = fr.b₁ ∧ elt 3 = fr.a₂ ∧ elt 4 = fr.b₂ ∧ elt 5 = fr.h₀ ∧
      elt 6 = fr.σ := by
  have h0 := hg 0 (by norm_num)
  have h1 := hg 1 (by norm_num)
  have h2 := hg 2 (by norm_num)
  have h3 := hg 3 (by norm_num)
  have h4 := hg 4 (by norm_num)
  have h5 := hg 5 (by norm_num)
  rw [sGen_zero] at h0
  rw [sGen_one] at h1
  rw [sGen_two] at h2
  rw [sGen_three] at h3
  rw [sGen_four] at h4
  rw [sGen_five] at h5
  exact ⟨h0, h1, h2, h3, h4, h5⟩

theorem f13_prods (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s) :
    elt (atR Q 2) = fr.z ∧ elt (mulE P 1 3) = fr.a₁ * fr.a₂ ∧
      elt (mulE P 2 4) = fr.b₁ * fr.b₂ ∧ elt (mulE P 1 4) = fr.a₁ * fr.b₂ ∧
      elt (mulE P (mulE P 1 2) 3) = fr.a₁ * fr.b₁ * fr.a₂ ∧
      elt (mulE P 5 6) = fr.h₀ * fr.σ ∧ elt (mulE P 2 6) = fr.b₁ * fr.σ := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := f13_gens hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR.sq (i := 2) (by norm_num), e2]
    exact (pow_two _).symm
  · rw [mulE_elt hR (x := 1) (y := 3) (by norm_num) (by norm_num), e1, e3]
  · rw [mulE_elt hR (x := 2) (y := 4) (by norm_num) (by norm_num), e2, e4]
  · rw [mulE_elt hR (x := 1) (y := 4) (by norm_num) (by norm_num), e1, e4]
  · rw [mulE_elt hR (x := mulE P 1 2) (y := 3) (f13_mulE_lt _ _ _) (by norm_num),
      mulE_elt hR (x := 1) (y := 2) (by norm_num) (by norm_num), e1, e2, e3]
  · rw [mulE_elt hR (x := 5) (y := 6) (by norm_num) (by norm_num), e5, e6]
  · rw [mulE_elt hR (x := 2) (y := 6) (by norm_num) (by norm_num), e2, e6]

theorem f13_coset (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    {S R : ℕ} (hS : mset elt S = (fr.S : Set Γ)) (h : f13CosetK P C V Q S 1 2 3 4 6 R = true) :
    centEl fr.S fr.σ = closure {fr.a₁ * fr.a₂, fr.b₁ * fr.b₂, fr.z} ∧
    {y : Γ | (∃ s ∈ fr.S, y = s * fr.σ) ∧ orderOf y = 2} =
      {y : Γ | ∃ c ∈ centEl fr.S fr.σ, y = c * fr.σ} ∧
    {y : Γ | ∃ c ∈ centEl fr.S fr.σ, y = c * fr.σ} = conjClass fr.S fr.σ := by
  obtain ⟨-, -, -, -, -, e6⟩ := f13_gens hg
  obtain ⟨hz, h13, h24, -, -, -, -⟩ := f13_prods hR hg
  simp only [f13CosetK, bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hF, h1, h2, h3⟩ := h
  have h6 : (6 : ℕ) < 128 := by norm_num
  have hcs := f13_cenE hR hS h6
  rw [e6] at hcs
  have hcg := f13_right hR hcs h6
  rw [e6] at hcg
  refine ⟨?_, ?_, ?_⟩
  · apply SetLike.coe_injective
    have hl : ∀ g ∈ [mulE P 1 3, mulE P 2 4, atR Q 2], g < 128 := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      exacts [f13_mulE_lt _ _ _, f13_mulE_lt _ _ _, atR_lt _ _]
    rw [← hcs, h1, closK_closure hR hl hF, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, hz, h13, h24]
    rw [f13_setOf_three]
  · have hL := involM_mset hR (Q := Q) (imgR (rowT C 6) S)
    rw [f13_right hR hS h6, e6] at hL
    have hL' : mset elt (involM Q (imgR (rowT C 6) S)) =
        {y : Γ | (∃ s ∈ fr.S, y = s * fr.σ) ∧ orderOf y = 2} := by
      rw [hL]
      ext y
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, f13_orderOf_eq_two_iff]
    exact hL'.symm.trans ((congrArg (mset elt) h2).trans hcg)
  · have hcl := f13_clsE hR (V := V) hS h6
    rw [e6] at hcl
    exact hcg.symm.trans ((congrArg (mset elt) h3).trans hcl)

@[expose] noncomputable def f13_rep (P Q : ℕ) : Fin 7 → ℕ :=
  ![atR Q 2, mulE P 2 4, mulE P 1 3, mulE P 1 4, mulE P (mulE P 1 2) 3, 5, 6]

theorem f13_rep_list : List.ofFn (f13_rep P Q) = reps13K P (atR Q 2) 1 2 3 4 5 6 := rfl

theorem f13_rep_lt (i : Fin 7) : f13_rep P Q i < 128 := by
  fin_cases i
  exacts [atR_lt _ _, f13_mulE_lt _ _ _, f13_mulE_lt _ _ _, f13_mulE_lt _ _ _,
    f13_mulE_lt _ _ _, by simp [f13_rep], by simp [f13_rep]]

theorem f13_rep_elt (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    (i : Fin 7) : elt (f13_rep P Q i) = fr.reps13 i := by
  obtain ⟨-, -, -, -, e5, e6⟩ := f13_gens hg
  obtain ⟨hz, h13, h24, h14, h123, -, -⟩ := f13_prods hR hg
  fin_cases i
  · exact hz
  · exact h24
  · exact h13
  · exact h14
  · exact h123
  · exact e5
  · exact e6

theorem f13_classes (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    {Ss : ℕ} (hSs : mset elt Ss = (fr.Sσ : Set Γ))
    (h : f13ClassK P C V Q Ss 1 2 3 4 5 6 = true) :
    {C : Set Γ | ∃ y ∈ invols fr.Sσ, C = conjClass fr.Sσ y} =
      Set.range (fun i => conjClass fr.Sσ (fr.reps13 i)) ∧
    Function.Injective (fun i => conjClass fr.Sσ (fr.reps13 i)) := by
  simp only [f13ClassK, strictB_eq] at h
  rw [← f13_rep_list] at h
  have hlt : ∀ r ∈ List.ofFn (f13_rep P Q), r < 128 := by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hr
    exact f13_rep_lt i
  obtain ⟨hmem, hcov, hdist⟩ := repsOK_sound hR hlt h
  have hI := f13_involM hR (Q := Q) hSs
  constructor
  · ext D
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hI] at hy
      obtain ⟨r, hr, x, hx, hxy⟩ := hcov y hy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hr
      refine ⟨i, (f13_conjClass_eq_of_mem ?_).symm⟩
      rw [hSs] at hx
      exact ⟨x, hx, by rw [← hxy, f13_rep_elt hR hg i]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨fr.reps13 i, ?_, rfl⟩
      rw [← hI, ← f13_rep_elt hR hg i]
      exact hmem _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  · intro i j hij
    rw [List.map_ofFn] at hdist
    have hinj : Function.Injective (clsE P C V Ss ∘ f13_rep P Q) := List.nodup_ofFn.1 hdist
    apply hinj
    apply eq_of_mset_eq hR.inj (fun k hk => testBit_clsE_lt hk) (fun k hk => testBit_clsE_lt hk)
    rw [f13_clsE hR hSs (f13_rep_lt i), f13_clsE hR hSs (f13_rep_lt j), f13_rep_elt hR hg i,
      f13_rep_elt hR hg j]
    exact hij

theorem f13_cent (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    {S Ss R : ℕ} (hS : mset elt S = (fr.S : Set Γ)) (hSs : mset elt Ss = (fr.Sσ : Set Γ))
    (h : f13CentK P C Q S Ss 1 2 3 4 5 6 R = true) :
    centEl fr.Sσ fr.z = fr.Sσ ∧
    centEl fr.Sσ (fr.b₁ * fr.b₂) = centEl fr.S (fr.b₁ * fr.b₂) ⊔ closure {fr.σ} ∧
    centEl fr.Sσ (fr.a₁ * fr.a₂) = centEl fr.S (fr.a₁ * fr.a₂) ⊔ closure {fr.σ} ∧
    centEl fr.Sσ (fr.a₁ * fr.b₂) = centEl fr.S (fr.a₁ * fr.b₂) ∧
    centEl fr.Sσ (fr.a₁ * fr.b₁ * fr.a₂) =
      centEl fr.S (fr.a₁ * fr.b₁ * fr.a₂) ⊔ closure {fr.h₀ * fr.σ} ∧
    centEl fr.Sσ fr.h₀ = centEl fr.S fr.h₀ ⊔ closure {fr.b₁ * fr.σ} ∧
    centEl fr.Sσ fr.σ = centEl fr.S fr.σ ⊔ closure {fr.σ} := by
  obtain ⟨-, -, -, -, e5, e6⟩ := f13_gens hg
  obtain ⟨hz, h13, h24, h14, h123, h56, h26⟩ := f13_prods hR hg
  simp only [f13CentK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h
  have one : ∀ {g : ℕ}, g < 128 → ∀ x ∈ [g], x < 128 := by
    intro g hg x hx
    rw [List.mem_singleton] at hx
    rw [hx]
    exact hg
  have cl : ∀ g : ℕ, closure {x | ∃ k ∈ [g], elt k = x} = closure {elt g} := by
    intro g
    rw [f13_setOf_eq_map, List.map_cons, List.map_nil, f13_setOf_one]
  have h6 : (6 : ℕ) < 128 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [← hz, ← f13_cenE hR hSs (atR_lt _ _), c1, hSs]
  · have := f13_supCK hR hS hSs (f13_mulE_lt _ _ _) (one h6) c2
    rwa [cl, h24, e6] at this
  · have := f13_supCK hR hS hSs (f13_mulE_lt _ _ _) (one h6) c3
    rwa [cl, h13, e6] at this
  · apply SetLike.coe_injective
    rw [← h14, ← f13_cenE hR hSs (f13_mulE_lt _ _ _), c4, f13_cenE hR hS (f13_mulE_lt _ _ _)]
  · have := f13_supCK hR hS hSs (f13_mulE_lt _ _ _) (one (f13_mulE_lt _ _ _)) c5
    rwa [cl, h123, h56] at this
  · have := f13_supCK hR hS hSs (by norm_num) (one (f13_mulE_lt _ _ _)) c6
    rwa [cl, e5, h26] at this
  · have := f13_supCK hR hS hSs h6 (one h6) c7
    rwa [cl, e6] at this

theorem fact13_of_twin {fr : Frame Γ} {elt : ℕ → Γ} {P C V Q R : ℕ}
    (hR : RealT elt P C V Q)
    (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    (h : f13K P C V Q 1 2 3 4 5 6 R = true) : fr.Fact13 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := f13_gens hg
  simp only [f13K, bAnd_eq, strictB_eq, Bool.and_eq_true] at h
  obtain ⟨hc5, hc6, hco, hcl, hce⟩ := h
  have hS : mset elt (closK C [1, 2, 3, 4, 5] R) = (fr.S : Set Γ) := by
    rw [closK_closure hR (by decide) hc5, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4, e5]
    rw [f13_setOf_five]
    rfl
  have hSs : mset elt (closK C [1, 2, 3, 4, 5, 6] R) = (fr.Sσ : Set Γ) := by
    rw [closK_closure hR (by decide) hc6, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4, e5, e6]
    rw [f13_setOf_six]
    rfl
  have h1 := f13_coset hR hg hS hco
  have h2 := f13_classes hR hg hSs hcl
  have h3 := f13_cent hR hg hS hSs hce
  exact ⟨h1.1, h1.2.1, h1.2.2, h2.1, h2.2,
    h3.1, h3.2.1, h3.2.2.1, h3.2.2.2.1, h3.2.2.2.2.1, h3.2.2.2.2.2.1, h3.2.2.2.2.2.2⟩

end CFSG.KC.G2Three.Sec1T3

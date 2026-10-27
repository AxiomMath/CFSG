module

public import CFSG.GH74.E2.Cl2Cl3Defs
public import CFSG.GH74.E2.Cl2BPair
public import CFSG.GH74.E2.Cl2Weights

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

variable {Q : Type*} [Group Q] {a b : MulAut Q} {N : Subgroup Q}

private theorem mulAut_cube_apply {g : MulAut Q} (hg : g ^ 3 = 1) (x : Q) : g (g (g x)) = x := by
  have := congrArg (fun f : MulAut Q => f x) hg
  simpa [pow_succ, MulAut.mul_apply] using this

private theorem mulAut_inv_apply_of_cube {g : MulAut Q} (hg : g ^ 3 = 1) (x : Q) :
    g⁻¹ x = g (g x) := by
  rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, mulAut_cube_apply hg]

theorem BPair.swap (h : BPair Q a b) : BPair Q b a where
  a_cube := h.b_cube
  b_cube := h.a_cube
  comm := h.comm.symm
  sup_top := by rw [sup_comm]; exact h.sup_top
  inf_le := by rw [inf_comm]; exact h.inf_le
  a_ne := h.b_ne
  b_ne := h.a_ne

private theorem fixSub_inv (b : MulAut Q) : fixSub b⁻¹ = fixSub b := by
  ext x
  rw [mem_fixSub, mem_fixSub, MulAut.inv_apply, MulEquiv.symm_apply_eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem BPair.inv_right (h : BPair Q a b) : BPair Q a b⁻¹ where
  a_cube := h.a_cube
  b_cube := by rw [inv_pow, h.b_cube, inv_one]
  comm := (Commute.inv_right (show Commute a b from h.comm)).eq
  sup_top := by rw [fixSub_inv]; exact h.sup_top
  inf_le := by rw [fixSub_inv]; exact h.inf_le
  a_ne := h.a_ne
  b_ne := by rw [fixSub_inv]; exact h.b_ne

theorem Cl3.swap (h : Cl3 Q a b N) : Cl3 Q b a N where
  bpair := h.bpair.swap
  four := h.four
  N_central := h.N_central
  N_elem := h.N_elem
  N_ne := h.N_ne
  N_inva := h.N_invb
  N_invb := h.N_inva
  N_eq := h.N_eq
  N_simple := fun M hM hb ha => h.N_simple M hM ha hb

theorem Cl3.inv_right (h : Cl3 Q a b N) : Cl3 Q a b⁻¹ N where
  bpair := h.bpair.inv_right
  four := h.four
  N_central := h.N_central
  N_elem := h.N_elem
  N_ne := h.N_ne
  N_inva := h.N_inva
  N_invb := fun n hn => by
    rw [mulAut_inv_apply_of_cube h.bpair.b_cube]
    exact h.N_invb _ (h.N_invb n hn)
  N_eq := h.N_eq
  N_simple := fun M hM ha hb => h.N_simple M hM ha (fun x hx => by
    have : b x = b⁻¹ (b⁻¹ x) := by
      rw [mulAut_inv_apply_of_cube h.bpair.b_cube (b⁻¹ x),
        mulAut_inv_apply_of_cube h.bpair.b_cube x, mulAut_cube_apply h.bpair.b_cube (b x)]
    rw [this]
    exact hb _ (hb x hx))

section Basic

theorem Cl3.N_le_dsub (_hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) : N ≤ dsub Q := by
  rw [h.N_eq]
  exact Subgroup.commutator_le_left _ _

theorem Cl3.commutator_N_top (h : Cl3 Q a b N) : ⁅N, (⊤ : Subgroup Q)⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro g hg y _
  have := Subgroup.mem_center_iff.mp (h.N_central hg) y
  rw [commutatorElement_def, Subgroup.mem_bot]
  calc g * y * g⁻¹ * y⁻¹ = y * g * g⁻¹ * y⁻¹ := by rw [this]
    _ = 1 := by group

theorem Cl3.dsub_comm (_hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) :
    ∀ u ∈ dsub Q, ∀ v ∈ dsub Q, u * v = v * u := by
  have h1 : ⁅⁅(⊤ : Subgroup Q), dsub Q⁆, (⊤ : Subgroup Q)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (⊤ : Subgroup Q) (dsub Q), ← h.N_eq]
    exact h.commutator_N_top
  have h2 : ⁅⁅dsub Q, (⊤ : Subgroup Q)⁆, (⊤ : Subgroup Q)⁆ = ⊥ := by
    rw [← h.N_eq]
    exact h.commutator_N_top
  have h3 : ⁅⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆, dsub Q⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  intro u hu v hv
  have : ⁅u, v⁆ ∈ ⁅dsub Q, dsub Q⁆ := Subgroup.commutator_mem_commutator hu hv
  have h4 : ⁅dsub Q, dsub Q⁆ = ⊥ := h3
  rw [h4, Subgroup.mem_bot, commutatorElement_def] at this
  calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
    _ = v * u := by rw [this, one_mul]

theorem Cl3.comm_mem (_hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q) (z : Q) :
    ⁅u, z⁆ ∈ N := by
  rw [h.N_eq]
  exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_top z)

private theorem dsub_inv_aux (g : MulAut Q) {u : Q} (hu : u ∈ dsub Q) : g u ∈ dsub Q := by
  have h1 : (dsub Q).map (g : Q →* Q) = dsub Q := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (MulEquiv.surjective g)]
  rw [← h1]
  exact Subgroup.mem_map_of_mem _ hu

theorem Cl3.dsub_inva (_h : Cl3 Q a b N) : ∀ u ∈ dsub Q, a u ∈ dsub Q := fun _ hu =>
  dsub_inv_aux a hu

theorem Cl3.dsub_invb (_h : Cl3 Q a b N) : ∀ u ∈ dsub Q, b u ∈ dsub Q := fun _ hu =>
  dsub_inv_aux b hu

theorem Cl3.sq_cent (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q) (z : Q) :
    ⁅u, z * z⁆ = 1 := by
  have hn : ⁅u, z⁆ ∈ N := h.comm_mem hQ hu z
  have hc : z * ⁅u, z⁆ * z⁻¹ = ⁅u, z⁆ := by
    have := Subgroup.mem_center_iff.mp (h.N_central hn) z
    calc z * ⁅u, z⁆ * z⁻¹ = ⁅u, z⁆ * z * z⁻¹ := by rw [this]
      _ = ⁅u, z⁆ := by group
  have e : ⁅u, z * z⁆ = ⁅u, z⁆ * (z * ⁅u, z⁆ * z⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, hc]
  exact h.N_elem _ hn

theorem Cl3.dsub_ne_N (_hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) : dsub Q ≠ N := by
  intro heq
  apply h.N_ne
  have h1 := h.N_eq
  rw [heq] at h1
  calc N = ⁅N, (⊤ : Subgroup Q)⁆ := h1
    _ = ⊥ := h.commutator_N_top

end Basic

private theorem inv_iff_of_cube {g : MulAut Q} (hg : g ^ 3 = 1) {S : Subgroup Q}
    (hS : ∀ x ∈ S, g x ∈ S) (x : Q) : g x ∈ S ↔ x ∈ S := by
  refine ⟨fun hx => ?_, hS x⟩
  rw [← mulAut_cube_apply hg x]
  exact hS _ (hS _ hx)

theorem fixB_bot {G : Type*} [Group G] [Finite G] (hG2 : IsPGroup 2 G)
    (hc : ∀ x y : G, x * y = y * x) (h4 : FourGen G) {α β : MulAut G} (hG : BPair G α β) :
    fixSub α ⊓ fixSub β = ⊥ := by
  classical
  have hA : AbInv2 α β (⊤ : Subgroup G) :=
    ⟨fun x _ y _ => hc x y, fun _ _ => Subgroup.mem_top _, fun _ _ => Subgroup.mem_top _⟩
  set T := wsub α β (⊤ : Subgroup G) hA .w0 with hT
  have hTle : fixSub α ⊓ fixSub β ≤ T := fun x hx =>
    (mem_wsub_w0 hA).2 ⟨Subgroup.mem_top _, hx.1, hx.2⟩
  have hTfix : T ≤ fixSub α ⊓ fixSub β := fun x hx =>
    ⟨((mem_wsub_w0 hA).1 hx).2.1, ((mem_wsub_w0 hA).1 hx).2.2⟩
  have hTΦ : T ≤ frattini G := fun x hx => hG.fix_inf_le hG2 h4 (hTfix hx)
  have hSn : (sqsub (⊤ : Subgroup G)).Normal :=
    ⟨fun n hn g => by rwa [hc g n, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hΦS : frattini G ≤ sqsub (⊤ : Subgroup G) := by
    have h1 := frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective (sqsub (⊤ : Subgroup G)))
    have h2 : frattini (G ⧸ sqsub (⊤ : Subgroup G)) = ⊥ := by
      refine frattini_eq_bot_of_exponent_two (fun x y => ?_) (fun x => ?_)
      · induction x using QuotientGroup.induction_on with
        | H g =>
          induction y using QuotientGroup.induction_on with
          | H g' => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
      · induction x using QuotientGroup.induction_on with
        | H g =>
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
          exact Subgroup.subset_closure ⟨g, Subgroup.mem_top _, rfl⟩
    rw [h2] at h1
    intro x hx
    have := h1 hx
    simpa [QuotientGroup.eq_one_iff] using this
  have hsq : ∀ t ∈ T, ∃ y0 ∈ T, t = y0 * y0 := by
    intro t ht
    obtain ⟨y, -, hy⟩ := (mem_sqsub_iff (fun x _ y _ => hc x y)).1 (hΦS (hTΦ ht))
    obtain ⟨y0, h0, ya, ha, yb, hb, yp, hp, ym, hm, rfl⟩ :=
      wsub_decomp hG2 hG.a_cube hG.b_cube hG.comm hA (Subgroup.mem_top y)
    have hsum : (t⁻¹ * (y0 * y0)) * (ya * ya) * (yb * yb) * (yp * yp) * (ym * ym) = 1 := by
      let _ : CommGroup G := { ‹Group G› with mul_comm := hc }
      have e : (t⁻¹ * (y0 * y0)) * (ya * ya) * (yb * yb) * (yp * yp) * (ym * ym) =
          t⁻¹ * ((y0 * ya * yb * yp * ym) * (y0 * ya * yb * yp * ym)) := by ac_rfl
      rw [e, ← hy, inv_mul_cancel]
    have hind := wsub_indep hG2 hG.a_cube hG.b_cube hG.comm hA
      (T.mul_mem (T.inv_mem ht) (T.mul_mem h0 h0))
      (Subgroup.mul_mem _ ha ha) (Subgroup.mul_mem _ hb hb) (Subgroup.mul_mem _ hp hp)
      (Subgroup.mul_mem _ hm hm) hsum
    exact ⟨y0, h0, (inv_mul_eq_one.mp hind.1)⟩
  have hTbot : T = ⊥ := by
    by_contra hne
    have hP : IsPGroup 2 T := hG2.to_subgroup T
    have hcard : 2 ∣ Nat.card T := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
      have hk0 : k ≠ 0 := by
        rintro rfl
        apply hne
        rw [Subgroup.eq_bot_iff_card]
        simpa using hk
      rw [hk]
      exact dvd_pow_self 2 hk0
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 hcard
    have hs1 : s ≠ 1 := fun h' => by
      rw [h', orderOf_one] at hs
      omega
    have hs2 : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rw [hs, sq] at this
      exact this
    let f : T → T := fun x => x * x
    have hfs : Function.Surjective f := fun t => by
      obtain ⟨y0, hy0, e⟩ := hsq t t.2
      exact ⟨⟨y0, hy0⟩, Subtype.ext e.symm⟩
    have hfi : Function.Injective f := Finite.injective_iff_surjective.mpr hfs
    have hff : f s = f 1 := by simp [f, hs2]
    exact hs1 (hfi hff)
  exact eq_bot_iff.2 (hTle.trans (le_of_eq hTbot))

theorem Cl3.fixB_le_dsub [Finite Q] (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) :
    fixSub a ⊓ fixSub b ≤ dsub Q := by
  have hDa : ∀ x, a x ∈ dsub Q ↔ x ∈ dsub Q := inv_iff_of_cube h.bpair.a_cube h.dsub_inva
  have hDb : ∀ x, b x ∈ dsub Q ↔ x ∈ dsub Q := inv_iff_of_cube h.bpair.b_cube h.dsub_invb
  have hDf : dsub Q ≤ frattini Q := dsub_le_frattini hQ
  have hG := h.bpair.quotient hQ (dsub Q) hDa hDb hDf
  have hG2 : IsPGroup 2 (Q ⧸ dsub Q) := hQ.to_quotient _
  have hc : ∀ x y : Q ⧸ dsub Q, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H g =>
      induction y using QuotientGroup.induction_on with
      | H g' =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hcomm : ⁅g'⁻¹, g⁻¹⁆ ∈ dsub Q :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        have e : (g * g')⁻¹ * (g' * g) = ⁅g'⁻¹, g⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hcomm
  have hbot := fixB_bot hG2 hc (h.four.quotient (dsub Q)) hG
  intro c hc'
  have hmem : (QuotientGroup.mk c : Q ⧸ dsub Q) ∈
      fixSub (quotAut a (dsub Q) hDa) ⊓ fixSub (quotAut b (dsub Q) hDb) := by
    rw [fixSub_quotAut hQ h.bpair.a_cube (dsub Q) hDa,
      fixSub_quotAut hQ h.bpair.b_cube (dsub Q) hDb]
    exact ⟨⟨c, hc'.1, rfl⟩, ⟨c, hc'.2, rfl⟩⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff c).1 hmem

theorem Cl3.eps_a_mem_dsub [Finite Q] (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {x : Q}
    (hx : x ∈ fixSub b) : eps a x ∈ dsub Q := by
  have hDa : ∀ x, a x ∈ dsub Q ↔ x ∈ dsub Q := inv_iff_of_cube h.bpair.a_cube h.dsub_inva
  have hDb : ∀ x, b x ∈ dsub Q ↔ x ∈ dsub Q := inv_iff_of_cube h.bpair.b_cube h.dsub_invb
  have hDf : dsub Q ≤ frattini Q := dsub_le_frattini hQ
  have hG := h.bpair.quotient hQ (dsub Q) hDa hDb hDf
  have hG2 : IsPGroup 2 (Q ⧸ dsub Q) := hQ.to_quotient _
  have hc : ∀ x y : Q ⧸ dsub Q, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H g =>
      induction y using QuotientGroup.induction_on with
      | H g' =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hcomm : ⁅g'⁻¹, g⁻¹⁆ ∈ dsub Q :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        have e : (g * g')⁻¹ * (g' * g) = ⁅g'⁻¹, g⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hcomm
  have hbot := fixB_bot hG2 hc (h.four.quotient (dsub Q)) hG
  set y : Q ⧸ dsub Q := QuotientGroup.mk x with hy
  have hmk : ∀ z, quotAut a (dsub Q) hDa (QuotientGroup.mk z) = QuotientGroup.mk (a z) :=
    fun z => quotAut_mk a (dsub Q) hDa z
  have hmkb : ∀ z, quotAut b (dsub Q) hDb (QuotientGroup.mk z) = QuotientGroup.mk (b z) :=
    fun z => quotAut_mk b (dsub Q) hDb z
  have h3 : ∀ z : Q, a (a (a z)) = z := mulAut_cube_apply h.bpair.a_cube
  have hab' : ∀ z : Q, a (b z) = b (a z) := fun z => by
    have := congrArg (fun f : MulAut Q => f z) h.bpair.comm
    simpa [MulAut.mul_apply] using this
  have hcm : ∀ u v : Q, (QuotientGroup.mk (u * v) : Q ⧸ dsub Q) = QuotientGroup.mk (v * u) :=
    fun u v => by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hc]
  have hfa : (QuotientGroup.mk (eps a x) : Q ⧸ dsub Q) ∈ fixSub (quotAut a (dsub Q) hDa) := by
    show quotAut a (dsub Q) hDa (QuotientGroup.mk (eps a x)) = QuotientGroup.mk (eps a x)
    rw [hmk]
    have e1 : a (eps a x) = (a x * a (a x)) * x := by
      unfold eps
      rw [map_mul, map_mul, h3]
    have e2 : eps a x = x * (a x * a (a x)) := by unfold eps; rw [mul_assoc]
    rw [e1, e2]
    exact hcm _ _
  have hfb : (QuotientGroup.mk (eps a x) : Q ⧸ dsub Q) ∈ fixSub (quotAut b (dsub Q) hDb) := by
    show quotAut b (dsub Q) hDb (QuotientGroup.mk (eps a x)) = QuotientGroup.mk (eps a x)
    rw [hmkb]
    have hbx : b x = x := hx
    have e1 : b (a x) = a x := by rw [← hab', hbx]
    have e2 : b (a (a x)) = a (a x) := by rw [← hab', ← hab', hbx]
    have : b (eps a x) = eps a x := by
      unfold eps
      rw [map_mul, map_mul, hbx, e1, e2]
    rw [this]
  have hmem : (QuotientGroup.mk (eps a x) : Q ⧸ dsub Q) ∈
      fixSub (quotAut a (dsub Q) hDa) ⊓ fixSub (quotAut b (dsub Q) hDb) := ⟨hfa, hfb⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff _).1 hmem

theorem Cl3.eps_b_mem_dsub [Finite Q] (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {y : Q}
    (hy : y ∈ fixSub a) : eps b y ∈ dsub Q :=
  Cl3.eps_a_mem_dsub hQ h.swap hy

end CFSG.GH74.E2

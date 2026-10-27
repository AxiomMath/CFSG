module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

structure ExcRef where
  node : ℕ
  w : Array ℕ
deriving Inhabited

@[expose] def childrenOK (n : ℕ) (cS : ArrCert) (nodes : Array Node) (cN : Array ArrCert)
    (i : ℕ) : Bool :=
  allLt cS.pts.size fun p =>
    !(eqA n (compA n cS.pts[p]! cS.pts[p]!) (idA n)) ||
      !(allLt nodes[i]!.basis.size fun k => commA n cS.pts[p]! nodes[i]!.basis[k]!) ||
      memA n cN[i]! cS.pts[p]! || childOK n nodes cN i cS.pts[p]! nodes[i]!.children[p]!

@[expose] def excOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inW : Array ℕ → Bool)
    (e0 : Array (Array ℕ)) (cN : Array ArrCert) (excs : List ExcRef) (i : ℕ) : Bool :=
  let c0 := enumBfs n e0 ps fuel
  enumOK n e0 ps c0 && excs.any fun r => r.node == i && validA n r.w && inW r.w &&
    (allLt e0.size fun j => memA n cN[i]! (conjA n r.w e0[j]!)) &&
      c0.pts.size == cN[i]!.pts.size

@[expose] def censusExcOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inX outX inW : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (sGens : Array (Array ℕ)) (roots : Array ℕ)
    (nodes : Array Node) (e0 : Array (Array ℕ)) (excs : List ExcRef) : Bool :=
  let cS := enumBfs n sGens ps fuel
  let cN := nodes.map fun nd => enumBfs n nd.basis ps fuel
  enumOK n sGens ps cS && (allLt cS.pts.size fun p => rootOK n nodes cN cS.pts[p]! roots[p]!) &&
    allLt nodes.size fun i => nodeOK n ps fuel inX outX allowPW allowInX allowU cS nodes cN i ||
      (enumOK n nodes[i]!.basis ps cN[i]! && excOK n ps fuel inW e0 cN excs i &&
        childrenOK n cS nodes cN i)

section Soundness

variable {n : ℕ} {X : Subgroup (Equiv.Perm (Fin n))} {inX outX : Array ℕ → Bool}

theorem monoW_of_le {W : Type*} [Group W] {X E₀ E : Subgroup W} {allowPW : Bool}
    (h : MonoW X allowPW E₀) (hle : E₀ ≤ E) : MonoW X allowPW E := by
  rcases h with ⟨w, hw, h4⟩ | ⟨hPW, hP⟩
  · exact Or.inl ⟨w, nE_mono X hle hw, h4⟩
  · exact Or.inr ⟨hPW, pWitness_of_le hle hP⟩

theorem census_node_of_censusExcOK {ps : List ℕ} {fuel : ℕ} {allowPW allowInX allowU : Bool}
    {sGens : Array (Array ℕ)} {roots : Array ℕ} {nodes : Array Node} {e0 : Array (Array ℕ)}
    {excs : List ExcRef} {inW : Array ℕ → Bool} (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (h : censusExcOK n ps fuel inX outX inW allowPW allowInX allowU sGens roots nodes e0 excs =
      true)
    {E : Subgroup (Equiv.Perm (Fin n))} (hES : E ≤ closure (permsA n sGens))
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) :
    MonoW X allowPW E ∨ ∃ i < nodes.size, nodeSub n nodes i = E ∧
      (witOK n ps fuel inX outX allowPW allowInX allowU nodes[i]!.basis
          (nodes.map fun nd => enumBfs n nd.basis ps fuel)[i]! nodes[i]!.wit = true ∨
        excOK n ps fuel inW e0 (nodes.map fun nd => enumBfs n nd.basis ps fuel) excs i =
          true) := by
  simp only [censusExcOK, Bool.and_eq_true] at h
  obtain ⟨⟨hS, hroot⟩, hnodes⟩ := h
  set cS := enumBfs n sGens ps fuel
  set cN := nodes.map fun nd => enumBfs n nd.basis ps fuel
  obtain ⟨hSmem, -, hSval⟩ := enumOK_spec hps hS
  have hnode : ∀ i < nodes.size,
      nodeOK n ps fuel inX outX allowPW allowInX allowU cS nodes cN i = true ∨
        (enumOK n nodes[i]!.basis ps cN[i]! = true ∧ excOK n ps fuel inW e0 cN excs i = true ∧
          childrenOK n cS nodes cN i = true) := by
    intro i hi
    have := allLt_spec hnodes hi
    simpa only [Bool.or_eq_true, Bool.and_eq_true, and_assoc] using this
  have hnodeE : ∀ i < nodes.size, enumOK n nodes[i]!.basis ps cN[i]! = true := by
    intro i hi
    rcases hnode i hi with h | h
    · simp only [nodeOK, Bool.and_eq_true] at h
      exact h.1.1
    · exact h.1
  have hbasis : ∀ i < nodes.size, ∀ k < nodes[i]!.basis.size,
      validA n nodes[i]!.basis[k]! = true := fun i hi k hk => enumOK_gens_valid (hnodeE i hi) hk
  have hmemN : ∀ i < nodes.size, ∀ {a : Array ℕ} {g : Equiv.Perm (Fin n)}, Rep n a g →
      memA n cN[i]! a = true → g ∈ nodeSub n nodes i :=
    fun i hi a g ha hm => enumOK_mem_of_any hps (hnodeE i hi) ha hm
  have hch : ∀ i < nodes.size, childrenOK n cS nodes cN i = true →
      ∀ u ∈ closure (permsA n sGens), u ^ 2 = 1 → u ∉ nodeSub n nodes i →
        (∀ x ∈ nodeSub n nodes i, x * u = u * x) →
          ∃ j < nodes.size, nodeSub n nodes j = nodeSub n nodes i ⊔ zpowers u := by
    intro i hi hc u hu hu2 hui hcomm
    obtain ⟨p, hp, rfl⟩ := (hSmem u).1 hu
    have hr := rep_of_validA (hSval p hp)
    have hcp := allLt_spec hc hp
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcp
    rcases hcp with ((h1 | h1) | h1) | h1
    · rw [(eqA_iff (rep_compA hr hr) rep_idA).2 (by rw [← sq]; exact hu2)] at h1
      exact Bool.noConfusion h1
    · have : (allLt nodes[i]!.basis.size fun k => commA n cS.pts[p]! nodes[i]!.basis[k]!) =
          true := by
        rw [allLt_iff]
        intro k hk
        have hbk := rep_of_validA (hbasis i hi k hk)
        exact (commA_iff hr hbk).2 (hcomm _ (subset_closure (mem_permsA hk))).symm
      rw [this] at h1
      exact Bool.noConfusion h1
    · exact absurd (hmemN i hi hr h1) hui
    · simp only [childOK, Bool.and_eq_true, decide_eq_true_eq] at h1
      obtain ⟨⟨⟨hj, hjb⟩, hib⟩, hu'⟩ := h1
      refine ⟨_, hj, le_antisymm ?_ (sup_le ?_ (zpowers_le.mpr (hmemN _ hj hr hu')))⟩
      · rw [nodeSub, closure_le]
        rintro _ ⟨k, hk, rfl⟩
        dsimp only
        have hbk := rep_of_validA (hbasis _ hj k hk)
        have h2 := allLt_spec hjb hk
        simp only [Bool.or_eq_true] at h2
        rw [SetLike.mem_coe]
        rcases h2 with h2 | h2
        · exact mem_sup_left (hmemN i hi hbk h2)
        · have hm := hmemN i hi (rep_compA hr hbk) h2
          rw [show permOfArr n nodes[nodes[i]!.children[p]!]!.basis[k]! =
              (permOfArr n cS.pts[p]!)⁻¹ * (permOfArr n cS.pts[p]! *
                permOfArr n nodes[nodes[i]!.children[p]!]!.basis[k]!) by group]
          exact mul_mem (mem_sup_right (inv_mem (mem_zpowers _))) (mem_sup_left hm)
      · rw [nodeSub, closure_le]
        rintro _ ⟨k, hk, rfl⟩
        exact hmemN _ hj (rep_of_validA (hbasis i hi k hk)) (allLt_spec hib hk)
  refine forall_of_tree (S := closure (permsA n sGens))
    (fun E => MonoW X allowPW E ∨ ∃ i < nodes.size, nodeSub n nodes i = E ∧
      (witOK n ps fuel inX outX allowPW allowInX allowU nodes[i]!.basis cN[i]! nodes[i]!.wit =
          true ∨ excOK n ps fuel inW e0 cN excs i = true))
    (MonoW X allowPW) (fun E₀ E hm hle _ _ _ => Or.inl (monoW_of_le hm hle))
    (nodeSub n nodes) nodes.size ?_ ?_ ?_ hES hE hE4
  ·
    intro a ha ha2 ha1
    obtain ⟨p, hp, rfl⟩ := (hSmem a).1 ha
    have hr := rep_of_validA (hSval p hp)
    have := allLt_spec hroot hp
    simp only [rootOK, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      decide_eq_true_eq] at this
    rcases this with (h1 | h1) | ⟨⟨hj, hall⟩, hu⟩
    · rw [(eqA_iff (rep_compA hr hr) rep_idA).2 (by rw [← sq]; exact ha2)] at h1
      exact Bool.noConfusion h1
    · exact absurd (eq_of_eqA hr rep_idA h1) ha1
    · refine ⟨_, hj, le_antisymm ?_ (zpowers_le.mpr (hmemN _ hj hr hu))⟩
      rw [nodeSub, closure_le]
      rintro _ ⟨k, hk, rfl⟩
      dsimp only
      have hbk := rep_of_validA (hbasis _ hj k hk)
      have h2 := allLt_spec hall hk
      simp only [Bool.or_eq_true] at h2
      rcases h2 with h2 | h2
      · rw [SetLike.mem_coe, eq_of_eqA hbk hr h2]
        exact mem_zpowers _
      · rw [SetLike.mem_coe, eq_of_eqA hbk rep_idA h2]
        exact one_mem _
  ·
    intro i hi
    rcases hnode i hi with hn | ⟨-, -, hc⟩
    · simp only [nodeOK, Bool.and_eq_true, Bool.or_eq_true] at hn
      obtain ⟨⟨hEi, hwit⟩, hch'⟩ := hn
      rcases witOK_sound hps hin hout hEi hwit with hm | ⟨hnm, -⟩
      · exact Or.inl hm
      rcases hch' with hm | hch'
      · rw [hnm] at hm
        exact Bool.noConfusion hm
      · exact Or.inr (hch i hi hch')
    · exact Or.inr (hch i hi hc)
  ·
    intro i hi _
    refine Or.inr (Or.inr ⟨i, hi, rfl, ?_⟩)
    rcases hnode i hi with hn | ⟨-, hx, -⟩
    · simp only [nodeOK, Bool.and_eq_true] at hn
      exact Or.inl hn.1.2
    · exact Or.inr hx

theorem eq_map_of_excOK {ps : List ℕ} {fuel : ℕ} {nodes : Array Node} {e0 : Array (Array ℕ)}
    {excs : List ExcRef} {Wg : Subgroup (Equiv.Perm (Fin n))} {inW : Array ℕ → Bool}
    (hps : ∀ p ∈ ps, p < n)
    (hinW : ∀ a, validA n a = true → inW a = true → permOfArr n a ∈ Wg) {i : ℕ}
    (hi : i < nodes.size)
    (hE : enumOK n nodes[i]!.basis ps (nodes.map fun nd => enumBfs n nd.basis ps fuel)[i]! = true)
    (hx : excOK n ps fuel inW e0 (nodes.map fun nd => enumBfs n nd.basis ps fuel) excs i = true) :
    ∃ w ∈ Wg, nodeSub n nodes i = (closure (permsA n e0)).map (MulAut.conj w).toMonoidHom := by
  simp only [excOK, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hx
  obtain ⟨h0, r, -, ⟨⟨⟨⟨hri, hv⟩, hw⟩, hconj⟩, hsize⟩⟩ := hx
  subst hri
  refine ⟨permOfArr n r.w, hinW _ hv hw, ?_⟩
  have hle : (closure (permsA n e0)).map (MulAut.conj (permOfArr n r.w)).toMonoidHom ≤
      nodeSub n nodes r.node := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have hrj := rep_of_validA (enumOK_gens_valid h0 hj)
    have hc := rep_conjA hv hrj
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SetLike.mem_coe]
    exact enumOK_mem_of_any hps hE hc (allLt_spec hconj hj)
  obtain ⟨-, h0card, -⟩ := enumOK_spec hps h0
  obtain ⟨-, hicard, -⟩ := enumOK_spec hps hE
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective (MulAut.conj (permOfArr n r.w)).injective]
  change Nat.card (closure (permsA n nodes[r.node]!.basis)) ≤ _
  rw [hicard, h0card, hsize]

theorem census_of_censusExcOK {ps : List ℕ} {fuel : ℕ} {allowPW allowInX allowU : Bool}
    {sGens : Array (Array ℕ)} {roots : Array ℕ} {nodes : Array Node} {e0 : Array (Array ℕ)}
    {excs : List ExcRef} {Wg : Subgroup (Equiv.Perm (Fin n))} {inW : Array ℕ → Bool}
    (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (hinW : ∀ a, validA n a = true → inW a = true → permOfArr n a ∈ Wg)
    (h : censusExcOK n ps fuel inX outX inW allowPW allowInX allowU sGens roots nodes e0 excs =
      true)
    {E : Subgroup (Equiv.Perm (Fin n))} (hES : E ≤ closure (permsA n sGens))
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) :
    WitW X allowPW allowInX allowU E ∨
      ∃ w ∈ Wg, E = (closure (permsA n e0)).map (MulAut.conj w).toMonoidHom := by
  have h' := h
  simp only [censusExcOK, Bool.and_eq_true] at h'
  obtain ⟨⟨-, -⟩, hnodes⟩ := h'
  rcases census_node_of_censusExcOK hps hin hout h hES hE hE4 with hm | ⟨i, hi, rfl, hw | hx⟩
  · exact Or.inl (witW_of_monoW allowInX allowU hm le_rfl)
  · have hEi : enumOK n nodes[i]!.basis ps (nodes.map fun nd => enumBfs n nd.basis ps fuel)[i]! =
        true := by
      have := allLt_spec hnodes hi
      simp only [Bool.or_eq_true, Bool.and_eq_true, nodeOK] at this
      rcases this with h1 | h1
      · exact h1.1.1
      · exact h1.1.1
    rcases witOK_sound hps hin hout hEi hw with hm | ⟨-, hw'⟩
    · exact Or.inl (witW_of_monoW allowInX allowU hm le_rfl)
    · exact Or.inl (hw' hE4)
  · have hEi : enumOK n nodes[i]!.basis ps (nodes.map fun nd => enumBfs n nd.basis ps fuel)[i]! =
        true := by
      have := allLt_spec hnodes hi
      simp only [Bool.or_eq_true, Bool.and_eq_true, nodeOK] at this
      rcases this with h1 | h1
      · exact h1.1.1
      · exact h1.1.1
    obtain ⟨w, hw, heq⟩ := eq_map_of_excOK hps hinW hi hEi hx
    exact Or.inr ⟨w, hw, heq⟩

end Soundness

@[expose] def rdExcR (tk : Array ℕ) (regs : Array (Array ℕ)) (p : ℕ) : ExcRef × ℕ :=
  (⟨tk[p]!, regs[tk[p + 1]!]!⟩, p + 2)

@[expose] def decodeExcR (regs : Array (Array ℕ)) (s : String) : List ExcRef :=
  (rdListC (decodeNats s) (rdExcR (decodeNats s) regs) 0).1

section Pair

@[expose] def ExcClass {n : ℕ} (R E₀ : Subgroup (Equiv.Perm (Fin n))) (E : Subgroup ↥R) : Prop :=
  ∃ w ∈ R, E.map R.subtype = E₀.map (MulAut.conj w).toMonoidHom

variable {n : ℕ} {P R E₀ : Subgroup (Equiv.Perm (Fin n))}

theorem excClass_of_map_conj {E : Subgroup ↥R} {w : ↥R}
    (h : ExcClass R E₀ (E.map (MulAut.conj w).toMonoidHom)) : ExcClass R E₀ E := by
  obtain ⟨v, hvR, hv⟩ := h
  refine ⟨(w : Equiv.Perm (Fin n))⁻¹ * v, R.mul_mem (R.inv_mem w.2) hvR, ?_⟩
  have key : (E.map (MulAut.conj w).toMonoidHom).map R.subtype =
      (E.map R.subtype).map (MulAut.conj (w : Equiv.Perm (Fin n))).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
  rw [key] at hv
  calc E.map R.subtype
      = ((E.map R.subtype).map (MulAut.conj (w : Equiv.Perm (Fin n))).toMonoidHom).map
          (MulAut.conj (w : Equiv.Perm (Fin n))⁻¹).toMonoidHom := by
        rw [map_map]
        conv_lhs => rw [← map_id (E.map R.subtype)]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
    _ = (E₀.map (MulAut.conj v).toMonoidHom).map
          (MulAut.conj (w : Equiv.Perm (Fin n))⁻¹).toMonoidHom := by rw [hv]
    _ = E₀.map (MulAut.conj ((w : Equiv.Perm (Fin n))⁻¹ * v)).toMonoidHom := by
        rw [map_map]
        congr 1

variable {testP : Array ℕ → Bool} {ps : List ℕ} {fuel : ℕ} {allowPW : Bool}
  {sGens : Array (Array ℕ)} {roots : Array ℕ} {nodes : Array Node} {e0 : Array (Array ℕ)}
  {excs : List ExcRef} {u : Array ℕ} {uR : Equiv.Perm (Fin n)} {k m : ℕ}

theorem witness_pair_exc_of_check (hPR : P ≤ R) (hps : ∀ p ∈ ps, p < n)
    (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P)) (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : censusExcOK n ps fuel testP testP (fun a => testP a || testP (compA n u a)) allowPW
      false false sGens roots nodes e0 excs = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    ∃ S : Subgroup ↥R, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness (P.subgroupOf R) E ∨ (allowPW = true ∧ PWitness (P.subgroupOf R) E) ∨
        ExcClass R (closure (permsA n e0)) E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (P.subgroupOf R).map R.subtype = P := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hPR]
  have hR : ∀ a, validA n a = true → (testP a || testP (compA n u a)) = true →
      permOfArr n a ∈ R := by
    intro a hv h
    have hr := rep_of_validA hv
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact hPR ((htest _ _ hr).1 h)
    · have h' := (htest _ _ (rep_compA hu hr)).1 h
      have : permOfArr n a = uR⁻¹ * (uR * permOfArr n a) := by group
      rw [this]
      exact mul_mem (inv_mem huR) (hPR h')
  have hc' := hc
  simp only [censusExcOK, Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, -⟩, -⟩ := hc'
  set S' := closure (permsA n sGens)
  have hS'le : S' ≤ R.subtype.range := by
    rw [closure_le, range_subtype]
    rintro _ ⟨j, hj, rfl⟩
    exact hR _ (enumOK_gens_valid hS hj) (allLt_spec hgen hj)
  obtain ⟨-, hS'card, -⟩ := enumOK_spec hps hS
  set S := S'.comap R.subtype
  have hSmap : S.map R.subtype = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 2 ^ k := by
    rw [← card_map_of_injective R.subtype_injective, hSmap, hS'card, hsize]
  refine ⟨S, ?_, fun E hES hE hE4 => ?_⟩
  · rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hScard, fun h2 => ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, hcard] at h1
    have hidx : S.index = m := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) k) h1
    rw [hidx] at h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  · have hin : ∀ a, validA n a = true → testP a = true →
        permOfArr n a ∈ (P.subgroupOf R).map R.subtype := fun a hv ha => by
      rw [hmap]
      exact (htest _ _ (rep_of_validA hv)).1 ha
    have hout : ∀ a, validA n a = true → permOfArr n a ∈ (P.subgroupOf R).map R.subtype →
        testP a = true := fun a hv ha => by
      rw [hmap] at ha
      exact (htest _ _ (rep_of_validA hv)).2 ha
    have hES' : E.map R.subtype ≤ S' := hSmap ▸ map_mono hES
    have hw := census_of_censusExcOK hps hin hout hR hc hES' (isElemAbelian_map hE R.subtype)
      (by rwa [card_map_of_injective R.subtype_injective])
    rcases hw with (hw | hw | ⟨h, -⟩ | ⟨h, -⟩) | ⟨w, hwR, heq⟩
    · exact Or.inl ((yWitness_map_iff _ R.subtype_injective _ _).mp hw)
    · exact Or.inr (Or.inl ⟨hw.1, (pWitness_map_iff _ R.subtype_injective _ _).mp hw.2⟩)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact Or.inr (Or.inr ⟨w, hwR, heq⟩)

theorem yCensus17Exc_pair_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : censusExcOK n ps fuel testP testP (fun a => testP a || testP (compA n u a)) true
      false false sGens roots nodes e0 excs = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus17 (P.subgroupOf R) (ExcClass R (closure (permsA n e0))) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_exc_of_check hPR hps htest hu huR hc hgen hsize hcard hm
  refine yCensus17_of_le_sylow hN hS (fun E w h => excClass_of_map_conj h)
    fun E hES hE hE4 hnot => ?_
  rcases hw E hES hE hE4 with h | ⟨-, h⟩ | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hnot

theorem yCensusExc_pair_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : censusExcOK n ps fuel testP testP (fun a => testP a || testP (compA n u a)) false
      false false sGens roots nodes e0 excs = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus (P.subgroupOf R) (ExcClass R (closure (permsA n e0))) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_exc_of_check hPR hps htest hu huR hc hgen hsize hcard hm
  refine yCensus_of_le_sylow hN hS (fun E w h => excClass_of_map_conj h)
    fun E hES hE hE4 hnot => ?_
  rcases hw E hES hE hE4 with h | ⟨h, -⟩ | h
  · exact h
  · exact absurd h (by decide)
  · exact absurd h hnot

end Pair

end CFSG.ComponentClassification.RankTwoSporadic.Cert

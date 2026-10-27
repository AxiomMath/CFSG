module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SAE8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertBMem
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelQ8Lib
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6iPerm
public import Certificates.Certificate517531

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

namespace CertB

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.Certificates CFSG.Sporadic.Schreier CFSG.EvenSmallLie.OmegaEight Certificates.AE6CertB
  Certificates.AE6Model CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

theorem wrAct_mul (a b : Wr 8) : wrAct (a * b) = wrAct a * wrAct b := by
  refine Equiv.ext fun x => ?_
  obtain ⟨i, s⟩ := x
  simp only [wrAct, Equiv.Perm.mul_apply, Equiv.prodShear_apply, Equiv.coe_addRight,
    Wr.mul_perm, Wr.mul_vec, Equiv.symm_apply_apply]
  refine Prod.ext rfl ?_
  show s + (a.vec (a.perm (b.perm i)) + b.vec (b.perm i)) =
    s + b.vec (b.perm i) + a.vec (a.perm (b.perm i))
  abel

theorem wrAct_one : wrAct (1 : Wr 8) = 1 := by
  refine Equiv.ext fun x => ?_
  obtain ⟨i, s⟩ := x
  simp only [wrAct, Equiv.prodShear_apply, Equiv.coe_addRight, Wr.one_perm, Wr.one_vec,
    Equiv.Perm.one_apply, Pi.zero_apply]
  refine Prod.ext rfl ?_
  show s + 0 = s
  rw [add_zero]

@[expose] def wrHom : Wr 8 →* Equiv.Perm (Fin 16) where
  toFun := wr16
  map_one' := by
    rw [wr16, wrAct_one]
    exact Equiv.permCongr_refl _
  map_mul' a b := by
    rw [wr16, wr16, wr16, wrAct_mul]
    exact Equiv.permCongr_mul _ _ _

theorem wrHom_apply (a : Wr 8) : wrHom a = wr16 a := rfl

theorem mkQ_allOnes : mkQ 8 (Wr.allOnes 8) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)

theorem wrHom_injective : Function.Injective wrHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker, wrHom_apply] at ha
  have key : ∀ i : Fin 8, wrAct a (i, 0) = (i, 0) := fun i => by
    have h := congrArg (fun f : Equiv.Perm (Fin 16) => wrPt.symm (f (wrPt (i, 0)))) ha
    simpa [wr16, Equiv.permCongr_apply] using h
  have hp : ∀ i, a.perm i = i := fun i => congrArg Prod.fst (key i)
  have hv : ∀ i, a.vec (a.perm i) = 0 := fun i => by
    have h := congrArg Prod.snd (key i)
    simpa [wrAct] using h
  have ha1 : a = 1 := Wr.ext (funext fun i => by rw [← hp i]; exact hv i) (Equiv.ext hp)
  rw [ha1]
  exact Subgroup.one_mem _

@[expose] noncomputable def grHom : Wr 8 × AE6Om →* Equiv.Perm (Fin 376) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 16 ⊕ Fin 360 ≃ Fin 376)).toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin 16) (Fin 360)).comp (wrHom.prodMap omegaT.subtype))

theorem grHom_injective : Function.Injective grHom :=
  (Equiv.permCongrHom _).injective.comp
    (Equiv.Perm.sumCongrHom_injective.comp (wrHom_injective.prodMap omegaT.subtype_injective))

end CertB

namespace CertB

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.Certificates CFSG.Sporadic.Schreier CFSG.EvenSmallLie.OmegaEight Certificates.AE6CertB
  Certificates.AE6Model CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

theorem ae6AEGen_eq : ae6AEGen = ae8Gen := rfl

theorem ae6AEGen_mem (i : Fin 7) : ae6AEGen i ∈ aeSub 8 := by
  rw [mem_aeSub]
  fin_cases i <;> refine ⟨?_, ?_⟩ <;>
    simp [ae6AEGen, Wr.wsum, Fin.sum_univ_eight, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap] <;>
    decide

theorem ae6AEGen_mul_self (i : Fin 7) : ae6AEGen i * ae6AEGen i = 1 := by
  revert i
  decide

theorem map_closure_ae6AEGen :
    (Subgroup.closure (Set.range ae6AEGen)).map wrHom = (ae8Q ()).originalSubgroup := by
  rw [ae8Q, certificate_originalSubgroup, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_range, Set.mem_setOf_eq, ae8Gens16, List.mem_map,
    List.mem_ofFn, tab_eq, wrHom_apply, ae6AEGen_eq]

theorem card_closure_ae6AEGen : Nat.card (Subgroup.closure (Set.range ae6AEGen)) = 2580480 := by
  rw [← Subgroup.card_map_of_injective wrHom_injective, map_closure_ae6AEGen, ae8Q,
    certificate_originalSubgroup]
  exact Certificates.certificate517531.1

theorem closure_ae6AEGen : Subgroup.closure (Set.range ae6AEGen) = aeSub 8 :=
  Subgroup.eq_of_le_of_card_ge ((Subgroup.closure_le _).mpr (by
    rintro _ ⟨i, rfl⟩
    exact ae6AEGen_mem i)) (by rw [A6h1.card_aeSub8, card_closure_ae6AEGen])

theorem closure_mkQ_ae6AEGen :
    Subgroup.closure (Set.range fun i => mkQ 8 (ae6AEGen i)) = (aeSub 8).map (mkQ 8) := by
  rw [← closure_ae6AEGen, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem exists_word {g : AEQ 8}
    (hg : g ∈ Subgroup.closure (Set.range fun i => mkQ 8 (ae6AEGen i))) :
    ∃ w : List (Fin 7), g = mkQ 8 (ae6AEWord w) := by
  have hinv : ∀ i, (mkQ 8 (ae6AEGen i))⁻¹ = mkQ 8 (ae6AEGen i) := fun i => by
    rw [← map_inv, inv_eq_of_mul_eq_one_right (ae6AEGen_mul_self i)]
  have hw : ∀ w : List (Fin 7),
      mkQ 8 (ae6AEWord w) = (w.map fun i => mkQ 8 (ae6AEGen i)).prod := fun w => by
    rw [ae6AEWord, map_list_prod, List.map_map]
    rfl
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨[i], by rw [hw]; simp⟩
  | one => exact ⟨[], by rw [hw]; simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u ++ v, by rw [hw, hw, hw, List.map_append, List.prod_append]⟩
  | inv x _ hx =>
    obtain ⟨u, rfl⟩ := hx
    refine ⟨u.reverse, ?_⟩
    rw [hw, hw, List.prod_inv_reverse, List.map_map, List.map_reverse]
    congr 2
    exact List.map_congr_left fun i _ => hinv i

end CertB

namespace CertB

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.Certificates CFSG.Sporadic.Schreier CFSG.EvenSmallLie.OmegaEight Certificates.AE6CertB
  Certificates.AE6Model CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

theorem v0Gens_eq : v0Gens () = [gen 0, gen 2, gen 3, gen 4, gen 5, gen 6, gen 7] := by
  simp only [v0Gens, ae8Letter, List.map_cons, List.map_nil]
  rw [curtisPerms_getD (by norm_num), curtisPerms_getD (by norm_num),
    curtisPerms_getD (by norm_num), curtisPerms_getD (by norm_num),
    curtisPerms_getD (by norm_num), curtisPerms_getD (by norm_num),
    curtisPerms_getD (by norm_num)]

theorem mem_v0Gens {g : Equiv.Perm (Fin 360)} :
    g ∈ v0Gens () ↔ ∃ i : Fin 8, i ≠ 1 ∧ gen i.val = g := by
  rw [v0Gens_eq]
  constructor
  · intro hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩, ⟨4, by decide, rfl⟩,
      ⟨5, by decide, rfl⟩, ⟨6, by decide, rfl⟩, ⟨7, by decide, rfl⟩]
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp_all

theorem map_ae6ModelV0 : (ae6ModelV 0).map omegaT.subtype = (v0Q ()).originalSubgroup := by
  rw [v0Q, certificate_originalSubgroup, ae6ModelV, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, mem_v0Gens]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨i, hi, rfl⟩, rfl⟩

theorem card_ae6ModelV0 : Nat.card (ae6ModelV 0) = 1290240 := by
  rw [← Subgroup.card_map_of_injective omegaT.subtype_injective, map_ae6ModelV0, v0Q,
    certificate_originalSubgroup]
  exact Certificates.certificate517531.2.1

@[expose] noncomputable def grSub : Subgroup (Wr 8 × AE6Om) :=
  Subgroup.closure (Set.range (fun i => (ae6AEGen i, A6.curtisGen (ae6V0Letter i))) ∪
    {(Wr.allOnes 8, 1)})

theorem mem_grGens {g : Equiv.Perm (Fin 376)} : g ∈ grGens () ↔
    (∃ i : Fin 7, grHom (ae6AEGen i, A6.curtisGen (ae6V0Letter i)) = g) ∨
      grHom (Wr.allOnes 8, 1) = g := by
  have hl : ∀ i : Fin 7, ae8Letter.getD i 0 = (ae6V0Letter i).val := by decide
  have e : ∀ i : Fin 7, tab (sumPerm (wr16 (ae8Gen i))
      ((curtisPerms ()).getD (ae8Letter.getD i 0) 1)) =
        grHom (ae6AEGen i, A6.curtisGen (ae6V0Letter i)) := fun i => by
    rw [tab_eq, hl, curtisPerms_getD (ae6V0Letter i).2]
    rfl
  have e2 : tab (sumPerm (wr16 (Wr.allOnes 8)) 1) = grHom (Wr.allOnes 8, 1) := by
    rw [tab_eq]
    rfl
  show g ∈ (List.ofFn fun i : Fin 7 => tab (sumPerm (wr16 (ae8Gen i))
      ((curtisPerms ()).getD (ae8Letter.getD i 0) 1))) ++
      [tab (sumPerm (wr16 (Wr.allOnes 8)) 1)] ↔ _
  rw [List.mem_append, List.mem_ofFn, List.mem_singleton, e2]
  simp only [Set.mem_range, e]
  constructor
  · rintro (⟨i, rfl⟩ | rfl)
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨i, rfl⟩ | rfl)
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr rfl

theorem map_grSub : grSub.map grHom = (grQ ()).originalSubgroup := by
  rw [grQ, certificate_originalSubgroup, grSub, MonoidHom.map_closure]
  congr 1
  ext g
  rw [Set.mem_setOf_eq, mem_grGens]
  simp only [Set.mem_image, Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, (⟨i, rfl⟩ | rfl), rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨_, Or.inl ⟨i, rfl⟩, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

theorem card_grSub : Nat.card grSub = 2580480 := by
  rw [← Subgroup.card_map_of_injective grHom_injective, map_grSub, grQ,
    certificate_originalSubgroup]
  exact Certificates.certificate517531.2.2.1

@[expose] noncomputable def grProj : Wr 8 × AE6Om →* AEQ 8 × AE6Om :=
  (mkQ 8).prodMap (MonoidHom.id AE6Om)

theorem map_grProj : grSub.map grProj =
    Subgroup.closure (Set.range fun i => (mkQ 8 (ae6AEGen i), A6.curtisGen (ae6V0Letter i))) := by
  rw [grSub, MonoidHom.map_closure, Set.image_union, Set.image_singleton, ← Set.range_comp]
  have h1 : grProj (Wr.allOnes 8, (1 : AE6Om)) = 1 := by
    simp only [grProj, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp,
      Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, mkQ_allOnes, MonoidHom.id_apply,
      Prod.mk_eq_one, and_self]
  rw [h1, Subgroup.closure_union, Subgroup.closure_singleton_one, sup_bot_eq]
  rfl

theorem ker_grProj : grProj.ker = (piSub 8).prod ⊥ := by
  rw [grProj, MonoidHom.ker_prodMap, QuotientGroup.ker_mk', MonoidHom.ker_id]

theorem ker_le_grSub : grProj.ker ≤ grSub := by
  rw [ker_grProj]
  rintro ⟨a, g⟩ ⟨ha, hg⟩
  have hg' : g = 1 := Subgroup.mem_bot.mp hg
  subst hg'
  rcases mem_piSub.mp ha with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (Or.inr rfl)

theorem card_ker_grProj : Nat.card grProj.ker = 2 := by
  rw [ker_grProj, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    A6h1.card_piSub8, Subgroup.card_bot]

theorem card_graph : Nat.card (Subgroup.closure
    (Set.range fun i => (mkQ 8 (ae6AEGen i), A6.curtisGen (ae6V0Letter i)))) = 1290240 := by
  have h := Subgroup.relIndex_mul_card grProj.ker grSub
  rw [Subgroup.relIndex_ker, inf_eq_left.mpr ker_le_grSub, card_ker_grProj, card_grSub] at h
  rw [← map_grProj]
  have h2 : Nat.card ↥(grSub.map grProj) * 2 = 1290240 * 2 := h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

theorem kQ8_pair : Q8Rel ((k0Gens ()).getD 0 1) ((k0Gens ()).getD 1 1) :=
  Certificates.certificate517531.2.2.2.1

theorem coe_kw1 : ((ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] : AE6Om) :
    Equiv.Perm (Fin 360)) = (k0Gens ()).getD 0 1 := by
  rw [coe_ae6Word]
  rfl

theorem coe_kw2 : ((ae6Word [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6] : AE6Om) :
    Equiv.Perm (Fin 360)) = (k0Gens ()).getD 1 1 := by
  rw [coe_ae6Word]
  rfl

theorem q8Rel_K0 : Q8Rel (ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] : AE6Om)
    (ae6Word [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6]) :=
  q8Rel_of_coe (by rw [coe_kw1, coe_kw2]; exact kQ8_pair)

theorem card_ae6ModelK : Nat.card ae6ModelK = 8 := by
  obtain ⟨e⟩ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert.nonempty_closure_pair_mulEquiv q8Rel_K0
  rw [ae6ModelK, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem diag_rels (c : Fin 2) :
    ∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6Diag c i)) r = 1 :=
  Certificates.certificate517531.2.2.2.2.1 c

theorem diag_twins (c : Fin 2) (s : Fin 3) :
    ae6Word ((ae6KWord s).map (ae6Diag c)) ∈ ae6Twin (ae6DiagTwin c) :=
  Certificates.certificate517531.2.2.2.2.2 c s

end CertB

namespace CertB

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE

theorem embed_emb_eq {α : Finset (Fin 8)} (h : α.card = 4) {f : Fin 4 → Fin 8}
    (hf : ∀ i, f i ∈ α) (hmono : StrictMono f) {k : Wr 4} {y : Wr 8}
    (h1 : ∀ i, y.vec (f i) = k.vec i) (h2 : ∀ i, y.perm (f i) = f (k.perm i))
    (h3 : ∀ x, x ∉ α → y.vec x = 0 ∧ y.perm x = x) : embed (emb α h) k = y := by
  have he := emb_apply_of_strictMono h hf hmono
  refine embed_eq_of_apply (fun i => ?_) (fun i => ?_) (fun x hx => h3 x ?_)
  · rw [he]
    exact h1 i
  · rw [he, he]
    exact h2 i
  · rw [range_emb] at hx
    exact hx

theorem mkQ_mem_memBar_of {α : Finset (Fin 8)} {h : α.card = 4} {P y : Wr 8} {k : Wr 4}
    (hk : k ∈ kList) (hy : embed (emb α h) k = y) (hP : y = P ∨ y = P * Wr.allOnes 8) :
    mkQ 8 P ∈ memBar α h true := by
  refine ⟨y, mem_memAt.mpr ⟨k, hk, hy⟩, ?_⟩
  rcases hP with rfl | rfl
  · rfl
  · rw [map_mul, mkQ_allOnes, mul_one]

theorem ae8_members (s : Fin 3) :
    mkQ 8 (ae6AEWord ((ae6KWord s).map ae6V0Index)) ∈ memBar ae6Alpha0 ae6Alpha0_card true := by
  have hf : ∀ i, (![2, 4, 5, 7] : Fin 4 → Fin 8) i ∈ ae6Alpha0 := by decide
  have hm : StrictMono (![2, 4, 5, 7] : Fin 4 → Fin 8) := by decide
  fin_cases s
  · exact mkQ_mem_memBar_of (k := ⟨vec4 [0, 3], d₂⟩) (by decide)
      (embed_emb_eq ae6Alpha0_card hf hm (y := ae6AEWord ((ae6KWord 0).map ae6V0Index))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)) (Or.inl rfl)
  · exact mkQ_mem_memBar_of (k := ⟨vec4 [2, 3], d₃⟩) (by decide)
      (embed_emb_eq ae6Alpha0_card hf hm
        (y := ae6AEWord ((ae6KWord 1).map ae6V0Index) * Wr.allOnes 8)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)) (Or.inr rfl)
  · exact mkQ_mem_memBar_of (k := ⟨vec4 [1, 3], d₁⟩) (by decide)
      (embed_emb_eq ae6Alpha0_card hf hm
        (y := ae6AEWord ((ae6KWord 2).map ae6V0Index) * Wr.allOnes 8)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)) (Or.inr rfl)

theorem ae8_conj (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool) (i : Fin 7) :
    ∃ (β : Finset (Fin 8)) (h' : β.card = 4) (c : Bool),
      conjSub (mkQ 8 (ae6AEGen i)) (memBar α h b) = memBar β h' c := by
  obtain ⟨c, hc⟩ := conjSub_memBar (ae6AEGen i) α h b
  exact ⟨_, _, c, hc⟩

theorem ae8_trans (α : Finset (Fin 8)) (h : α.card = 4)
    (b : Bool) : ∃ w : List (Fin 7),
      memBar α h b = conjSub (mkQ 8 (ae6AEWord w)) (memBar ae6Alpha0 ae6Alpha0_card true) := by
  obtain ⟨g, hg, he⟩ := exists_conjSub_memBar ae6Alpha0 ae6Alpha0_card true α h b
  rw [← closure_mkQ_ae6AEGen] at hg
  obtain ⟨w, rfl⟩ := exists_word hg
  exact ⟨w, he⟩

end CertB

theorem ae6AE8Fin_proved : AE6AE8Fin :=
  ⟨CertB.ae6AEGen_mem, CertB.closure_mkQ_ae6AEGen, A6h1.card_ae6AE8, CertB.card_ae6ModelV0,
    CertB.card_graph, CertB.card_ae6ModelK, CertB.ae8_members, CertB.ae8_conj, CertB.ae8_trans,
    fun c => ⟨CertB.diag_rels c, CertB.diag_twins c⟩⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

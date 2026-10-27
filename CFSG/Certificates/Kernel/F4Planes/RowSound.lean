module

public import Certificates.Data.Kernel.F4PlanesRow
public import CFSG.Certificates.Kernel.F4Planes.Model
public import CFSG.Certificates.Kernel.F4Syl3.RelSound
public import CFSG.RankThree.PartOne.SEITZX.F4Two
import all CFSG.Certificates.Kernel.F4SaltSound
import all CFSG.LieType.Simplicity.TitsBits

public section

namespace CFSG.KC.F4Planes

open CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX CFSG.KC.F4Salt CFSG.KC.Loop
  CFSG.KC.F4Syl3 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

variable {K : Type} [Field K]
  [CharP K 2]

theorem hasBitsS_of_eqS {g : adjointGroup ReeTag.F4.tag K} {A B : ℕ} (hg : HasBitsS K g A)
    (h : eqS A B = true) : HasBitsS K g B := by
  have e : toEnd K (A / 2 ^ 128) = toEnd K (B / 2 ^ 128) :=
    (toEnd_eq_toEnd_iff _ _).2 ((eqS_iff A B).1 h)
  have hg' : ((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) =
      toEnd K (A / 2 ^ 128) := hg
  change ((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) =
    toEnd K (B / 2 ^ 128)
  rw [hg', e]

theorem hasBitsS_inv_of {g : adjointGroup ReeTag.F4.tag K} {T Y : ℕ} (hg : HasBitsS K g T)
    (h : eqS (mulS T Y) oneS = true) : HasBitsS K g⁻¹ Y := by
  have e1 : toEnd K (mulS T Y / 2 ^ 128) = toEnd K (oneS / 2 ^ 128) :=
    (toEnd_eq_toEnd_iff _ _).2 ((eqS_iff _ _).1 h)
  rw [mulS_div, oneS_div, toEnd_mul, toEnd_oneBits] at e1
  have hg' : ((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) =
      toEnd K (T / 2 ^ 128) := hg
  rw [← hg'] at e1
  change ((g⁻¹ : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K).val = toEnd K (Y / 2 ^ 128)
  have hinv : ((g⁻¹ : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K).val *
      ((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  calc ((g⁻¹ : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K).val
      = ((g⁻¹ : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K).val *
          (((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) *
            toEnd K (Y / 2 ^ 128)) := by rw [e1, mul_one]
    _ = toEnd K (Y / 2 ^ 128) := by rw [← mul_assoc, hinv, one_mul]

variable (K) in
noncomputable abbrev wordE (W L : ℕ) : adjointGroup ReeTag.F4.tag K :=
  evalG K (wordOfCodes (decW8 W L))

variable (K) in
noncomputable abbrev pathE (gw gl p : List ℕ) : adjointGroup ReeTag.F4.tag K :=
  (p.map fun k => wordE K (gw.getD k 0) (gl.getD k 0)).prod

theorem hasBitsS_pathS (gw gl : List ℕ) : ∀ p : List ℕ, (∀ k ∈ p, k < 5) →
    HasBitsS K (pathE K gw gl p) (pathS [wordS (gw.getD 0 0) (gl.getD 0 0),
      wordS (gw.getD 1 0) (gl.getD 1 0), wordS (gw.getD 2 0) (gl.getD 2 0),
      wordS (gw.getD 3 0) (gl.getD 3 0), wordS (gw.getD 4 0) (gl.getD 4 0)] p)
  | [], _ => hasBitsS_one
  | k :: p, h => by
    have hk : k < 5 := h k List.mem_cons_self
    have ih := hasBitsS_pathS gw gl p fun j hj => h j (List.mem_cons_of_mem _ hj)
    rw [pathE, List.map_cons, List.prod_cons]
    refine HasBitsS.mul ?_ ih
    interval_cases k
    all_goals simp only [List.getD_cons_zero, List.getD_cons_succ]
    all_goals exact hasBitsS_wordS _ _

theorem pins_sound {gw gl pS : List ℕ} {paths : List (List ℕ)} (h : pinP gw gl paths pS = true)
    {i : ℕ} (hi : i < 6) : HasBitsS K (pathE K gw gl (paths.getD i [])) (pS.getD i 0) := by
  simp only [pinP, strictB_eq] at h
  have h' := allN_spec h i hi
  rw [Bool.and_eq_true] at h'
  have hp : ∀ k ∈ paths.getD i [], k < 5 := fun k hk => by
    have := allL_spec h'.1 k hk
    simpa using this
  exact hasBitsS_of_eqS (hasBitsS_pathS gw gl _ hp) h'.2

theorem pres_of_relP {s : Fin 4 → adjointGroup ReeTag.F4.tag K}
    {g4 g5 : adjointGroup ReeTag.F4.tag K} {pS : List ℕ}
    (hs : ∀ i : Fin 4, HasBitsS K (s i) (pS.getD i 0)) (h4 : HasBitsS K g4 (pS.getD 4 0))
    (h5 : HasBitsS K g5 (pS.getD 5 0)) (h : relP pS = true) : Pres s g4 g5 := by
  simp only [relP, strictB_eq] at h
  refine pres_of_relB (S := [pS.getD 0 0, pS.getD 1 0, pS.getD 2 0, pS.getD 3 0]) (fun i => ?_)
    h4 h5 h
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3
  · omega

theorem hasBitsS_phiS' {s : Fin 4 → adjointGroup ReeTag.F4.tag K}
    {g4 g5 : adjointGroup ReeTag.F4.tag K} {S : List ℕ} {G4 G5 : ℕ}
    (hs : ∀ i : Fin 4, HasBitsS K (s i) (S.getD i 0)) (h4 : HasBitsS K g4 G4)
    (h5 : HasBitsS K g5 G5) (m : ℕ) : HasBitsS K (phi s g4 g5 m) (phiS S G4 G5 m) :=
  (hasBitsS_fSS hs _).mul ((hasBitsS_powS h4 _).mul (hasBitsS_powS h5 _))

abbrev g6d : G6 := (0, 0, 0, 0, 0, 0)

variable (K) in
noncomputable def tokE (gs : List G6) (n k : ℕ) : adjointGroup ReeTag.F4.tag K :=
  if k < n then wordE K (gs.getD k g6d).1 (gs.getD k g6d).2.1
  else (wordE K (gs.getD (k - n) g6d).1 (gs.getD (k - n) g6d).2.1)⁻¹

theorem genB_spec {A B : ℕ} {g : G6} (h : genB A B g = true) :
    eqS (wordS g.1 g.2.1) g.2.2.2.2.1 = true ∧ eqS (mulS g.2.2.2.2.1 g.2.2.2.2.2) oneS = true ∧
      eqS (mulS (powS A g.2.2.1) (powS B g.2.2.2.1)) oneS = false ∧
      eqS (mulS g.2.2.2.2.1 (mulS (powS A g.2.2.1) (powS B g.2.2.2.1)))
        (mulS (mulS (powS A g.2.2.1) (powS B g.2.2.2.1)) g.2.2.2.2.1) = true := by
  simp only [genB, strictB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem hasBitsS_tokE {gs : List G6} (hg : ∀ g ∈ gs, HasBitsS K (wordE K g.1 g.2.1) g.2.2.2.2.1 ∧
    HasBitsS K (wordE K g.1 g.2.1)⁻¹ g.2.2.2.2.2) {k : ℕ} (hk : k < gs.length + gs.length) :
    HasBitsS K (tokE K gs gs.length k) (tokAt gs gs.length k) := by
  by_cases h : k < gs.length
  · have e : tokAt gs gs.length k = (gs.getD k g6d).2.2.2.2.1 := by
      have hb : Nat.blt k gs.length = true := by simpa using h
      rw [tokAt, hb]
    rw [e, tokE, if_pos h, List.getD_eq_getElem _ _ h]
    exact (hg _ (List.getElem_mem h)).1
  · have h' : k - gs.length < gs.length := by omega
    have e : tokAt gs gs.length k = (gs.getD (k - gs.length) g6d).2.2.2.2.2 := by
      have hb : Nat.blt k gs.length = false := by
        rw [Bool.eq_false_iff]
        intro hb
        exact h (by simpa using hb)
      rw [tokAt, hb]
      rfl
    rw [e, tokE, if_neg h, List.getD_eq_getElem _ _ h']
    exact (hg _ (List.getElem_mem h')).2

theorem hasBitsS_prodTok {gs : List G6} (hg : ∀ g ∈ gs,
    HasBitsS K (wordE K g.1 g.2.1) g.2.2.2.2.1 ∧ HasBitsS K (wordE K g.1 g.2.1)⁻¹ g.2.2.2.2.2) :
    ∀ idx : List ℕ, (∀ k ∈ idx, k < gs.length + gs.length) →
      HasBitsS K ((idx.map (tokE K gs gs.length)).prod) (prodTok gs gs.length idx)
  | [], _ => hasBitsS_one
  | k :: idx, h => by
    rw [List.map_cons, List.prod_cons]
    exact (hasBitsS_tokE hg (h k List.mem_cons_self)).mul
      (hasBitsS_prodTok hg idx fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem lenL_eq {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenL l) = _
    rw [lenL_eq l]
    rfl

theorem decW8_tw {t : ℕ} (ht : t < 8) : decW8 (twW t) (twL t) = targetWord t := by
  interval_cases t <;> rfl

theorem tgtB_spec {gs : List G6} {idx : List ℕ} {t : ℕ} (h : tgtB gs gs.length idx t = true) :
    (∀ k ∈ idx, k < gs.length + gs.length) ∧ eqS (prodTok gs gs.length idx) (wordS (twW t) (twL t))
      = true := by
  simp only [tgtB, Bool.and_eq_true] at h
  refine ⟨fun k hk => ?_, h.2⟩
  have := allL_spec h.1 k hk
  simpa using this

variable [Finite K]

theorem rowG_sound (hK : Nat.card K = 2) {s : Fin 4 → adjointGroup ReeTag.F4.tag K}
    {g4 g5 : adjointGroup ReeTag.F4.tag K} {S : List ℕ} {G4 G5 PR r : ℕ} {gs : List G6}
    {tg : List (List ℕ)} (hs : ∀ i : Fin 4, HasBitsS K (s i) (S.getD i 0))
    (h4 : HasBitsS K g4 G4) (h5 : HasBitsS K g5 G5) (h : rowG S G4 G5 PR gs tg r = true) :
    Subgroup.closure (zSet (planeR s g4 g5 PR r)) = ⊤ := by
  simp only [rowG, strictB_eq, Bool.and_eq_true, lenL_eq] at h
  obtain ⟨hgs, htg⟩ := h
  set a := phi s g4 g5 (aR PR r)
  set b := phi s g4 g5 (bR PR r)
  have hA : HasBitsS K a (phiS S G4 G5 (aR PR r)) := hasBitsS_phiS' hs h4 h5 _
  have hB : HasBitsS K b (phiS S G4 G5 (bR PR r)) := hasBitsS_phiS' hs h4 h5 _
  set E₀ := planeR s g4 g5 PR r
  have haE : a ∈ E₀ := Subgroup.subset_closure (Or.inl rfl)
  have hbE : b ∈ E₀ := Subgroup.subset_closure (Or.inr rfl)
  have hgen : ∀ g ∈ gs, (HasBitsS K (wordE K g.1 g.2.1) g.2.2.2.2.1 ∧
      HasBitsS K (wordE K g.1 g.2.1)⁻¹ g.2.2.2.2.2) ∧ wordE K g.1 g.2.1 ∈ zSet E₀ := by
    intro g hg
    obtain ⟨h1, h2, h3, h4'⟩ := genB_spec (allL_spec hgs g hg)
    have hC : HasBitsS K (wordE K g.1 g.2.1) g.2.2.2.2.1 := hasBitsS_of_eqS (hasBitsS_wordS _ _) h1
    have hE : HasBitsS K (a ^ g.2.2.1 * b ^ g.2.2.2.1)
        (mulS (powS (phiS S G4 G5 (aR PR r)) g.2.2.1) (powS (phiS S G4 G5 (bR PR r)) g.2.2.2.1)) :=
      (hasBitsS_powS hA _).mul (hasBitsS_powS hB _)
    refine ⟨⟨hC, hasBitsS_inv_of hC h2⟩, a ^ g.2.2.1 * b ^ g.2.2.2.1,
      mul_mem (pow_mem haE _) (pow_mem hbE _), fun e => ?_, ?_⟩
    · rw [(hE.eq_iff hasBitsS_one).1 e] at h3
      exact Bool.noConfusion h3
    · exact ((hC.mul hE).eq_iff (hE.mul hC)).2 h4'
  have htok : ∀ k, k < gs.length + gs.length → tokE K gs gs.length k ∈ Subgroup.closure (zSet E₀) := by
    intro k hk
    unfold tokE
    by_cases h : k < gs.length
    · rw [if_pos h, List.getD_eq_getElem _ _ h]
      exact Subgroup.subset_closure (hgen _ (List.getElem_mem h)).2
    · have h' : k - gs.length < gs.length := by omega
      rw [if_neg h, List.getD_eq_getElem _ _ h']
      exact inv_mem (Subgroup.subset_closure (hgen _ (List.getElem_mem h')).2)
  have htarg : ∀ t < 8, evalG K (wordOfCodes (targetWord t)) ∈ Subgroup.closure (zSet E₀) := by
    intro t ht
    obtain ⟨hidx, heq⟩ := tgtB_spec (allN_spec htg t ht)
    have hP := hasBitsS_prodTok (fun g hg => (hgen g hg).1) _ hidx
    have hW : HasBitsS K (evalG K (wordOfCodes (targetWord t))) (wordS (twW t) (twL t)) := by
      rw [← decW8_tw ht]
      exact hasBitsS_wordS _ _
    rw [← (hP.eq_iff hW).2 heq]
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact htok k (hidx k hk)
  rw [eq_top_iff, ← closure_xElement_yElement (τ := ReeTag.F4.tag) (K := K), Subgroup.closure_le]
  rintro _ ⟨i, c', rfl | rfl⟩
  · rcases eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · rw [xElement_zero]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htarg i.val (by omega)
      rwa [show targetWord i.val = targetWord (⟨i.val, hi⟩ : Fin 4).val from rfl,
        evalG_targetWord_x (K := K) ⟨i.val, hi⟩] at this
  · rcases eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · rw [show yElement (τ := ReeTag.F4.tag) (K := K) i 0 = 1 from
        Subtype.ext (Units.ext (yOp_zero i))]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htarg (i.val + 4) (by omega)
      rw [show targetWord (i.val + 4) = targetWord ((⟨i.val, hi⟩ : Fin 4).val + 4) from rfl,
        evalG_targetWord_y (K := K) ⟨i.val, hi⟩] at this
      rw [yElement_one_eq]
      exact this

theorem rowP_sound (hK : Nat.card K = 2) {s : Fin 4 → adjointGroup ReeTag.F4.tag K}
    {g4 g5 : adjointGroup ReeTag.F4.tag K} {pS : List ℕ} {PR r : ℕ} {gens : List (List G6)}
    {tgs : List (List (List ℕ))} (hs : ∀ i : Fin 4, HasBitsS K (s i) (pS.getD i 0))
    (h4 : HasBitsS K g4 (pS.getD 4 0)) (h5 : HasBitsS K g5 (pS.getD 5 0))
    (h : rowP pS PR gens tgs r = true) : Subgroup.closure (zSet (planeR s g4 g5 PR r)) = ⊤ := by
  simp only [rowP, strictB_eq] at h
  refine rowG_sound hK (S := [pS.getD 0 0, pS.getD 1 0, pS.getD 2 0, pS.getD 3 0]) (fun i => ?_)
    h4 h5 h
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3
  · omega

end CFSG.KC.F4Planes

end

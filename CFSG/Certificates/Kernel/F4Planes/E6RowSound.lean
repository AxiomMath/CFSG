
module

public import Certificates.Data.Kernel.F4PlanesE6
public import CFSG.Certificates.Kernel.E6SaltSound
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6TwoBase
import all CFSG.Certificates.Kernel.E6SaltSound

public section

namespace CFSG.KC.F4PlanesE6

open CFSG.KC.E6Salt CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two (letterOfCode6 wordOfCodes6 f4ToE6Letter
  orbitNodes iota_letter iota_xE iota_yE evalG6_x evalG6_xnx)

theorem strictB_eq6 (y : ℕ) (k : ℕ → Bool) : E6Salt.strictB y k = k y := by
  cases y <;> rfl

theorem allL_spec6 {α : Type} {f : α → Bool} :
    ∀ {l : List α}, E6Salt.allL l f = true → ∀ x ∈ l, f x = true
  | [], _, _, hx => absurd hx List.not_mem_nil
  | y :: l, h, x, hx => by
    change Bool.rec false (E6Salt.allL l f) (f y) = true at h
    cases hy : f y
    · rw [hy] at h
      exact absurd h Bool.false_ne_true
    · rw [hy] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hy
      · exact allL_spec6 h x hx

theorem lenL_eq6 {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenL l) = _
    rw [lenL_eq6 l]
    rfl

theorem lt_of_blt {a b : ℕ} (h : Nat.blt a b = true) : a < b := by
  rw [Nat.blt_eq] at h
  exact h

theorem blt_true {a b : ℕ} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem blt_false {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.2 fun hb => h (lt_of_blt hb)

theorem eqS_symm {A B : ℕ} (h : eqS A B = true) : eqS B A = true := by
  rw [eqS_iff] at h ⊢
  exact h.symm

theorem decW_three (W : ℕ) : ∀ L, decW 3 W L = CFSG.KC.F4Salt.decW8 W L
  | 0 => rfl
  | L + 1 => by
    rw [decW, CFSG.KC.F4Salt.decW8, decW_three W L]
    rfl

theorem decW_tgW : decW 4 (tgW 0) (tgL 0) = [0] ∧ decW 4 (tgW 1) (tgL 1) = [2] ∧
    decW 4 (tgW 2) (tgL 2) = [0, 6 + 0, 0] ∧ decW 4 (tgW 3) (tgL 3) = [2, 6 + 2, 2] := by
  decide

section Sound

variable {K : Type} [Field K] [CharP K 2]

theorem hasBitsS_inv_of {g : adjointGroup Tag.E6 K} {T Y : ℕ} (hg : HasBitsS K g T)
    (h : eqS (mulS T Y) oneS = true) : HasBitsS K g⁻¹ Y := by
  have e1 : E6Bits.toEnd K (mulS T Y / 2 ^ 192) = E6Bits.toEnd K (oneS / 2 ^ 192) :=
    (E6Bits.toEnd_eq_toEnd_iff _ _).2 ((eqS_iff _ _).1 h)
  rw [mulS_div, oneS_div, E6Bits.toEnd_mul, E6Bits.toEnd_oneBits] at e1
  have hg' : ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) =
      E6Bits.toEnd K (T / 2 ^ 192) := hg
  rw [← hg'] at e1
  change ((g⁻¹ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K).val = E6Bits.toEnd K (Y / 2 ^ 192)
  have hinv : ((g⁻¹ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K).val *
      ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  calc ((g⁻¹ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K).val
      = ((g⁻¹ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K).val *
          (((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) *
            E6Bits.toEnd K (Y / 2 ^ 192)) := by rw [e1, mul_one]
    _ = E6Bits.toEnd K (Y / 2 ^ 192) := by rw [← mul_assoc, hinv, one_mul]

theorem evalG_codes (w : List ℕ) :
    E6Bits.evalG K (w.map E6Salt.letterOfCode) = E6Bits.evalG K (wordOfCodes6 w) :=
  rfl

variable (K) in
noncomputable abbrev iotaL (c : ℕ) : adjointGroup Tag.E6 K :=
  embE6F4 K ((CFSG.RankThree.PartOne.SEITZX.letterOfCode c).elt K)

theorem iota_sound {LP IP IPi : ℕ} {iw il : List ℕ} (hL : letOK LP = true)
    (h : iotaB LP IP IPi iw il = true)
    (hw : ∀ c < 8, decW 4 (iw.getD c 0) (il.getD c 0) = f4ToE6Letter c) {c : ℕ} (hc : c < 8) :
    HasBitsS K (iotaL K c) (letT IP c) ∧ HasBitsS K (iotaL K c)⁻¹ (letT IPi c) := by
  have h' := allN_spec h c hc
  rw [strictB_eq6, Bool.and_eq_true] at h'
  have hW : HasBitsS K (iotaL K c) (wordS LP 4 (iw.getD c 0) (il.getD c 0)) := by
    have e := hasBitsS_wordS_letters (K := K) hL (iw.getD c 0) (il.getD c 0)
    rw [hw c hc, evalG_codes, ← iota_letter hc] at e
    exact e
  have hI := hW.of_eqS (eqS_symm h'.1)
  exact ⟨hI, hasBitsS_inv_of hI h'.2⟩

theorem iota_wordE (W L : ℕ) :
    embE6F4 K (CFSG.KC.F4Planes.wordE K W L) = ((decW 3 W L).map (iotaL K)).prod := by
  rw [decW_three]
  refine (map_list_prod (embE6F4 K) ((CFSG.RankThree.PartOne.SEITZX.wordOfCodes
    (CFSG.KC.F4Salt.decW8 W L)).map (CFSG.LieType.Simplicity.TitsBits.Letter.elt K))).trans ?_
  simp only [CFSG.RankThree.PartOne.SEITZX.wordOfCodes, List.map_map]
  rfl

theorem hasBitsS_iota_pathE {IP : ℕ} (hI : ∀ c < 8, HasBitsS K (iotaL K c) (letT IP c))
    (gw gl : List ℕ) : ∀ p : List ℕ, (∀ k ∈ p, k < 5) →
    HasBitsS K (embE6F4 K (CFSG.KC.F4Planes.pathE K gw gl p))
      (pathE [wordS IP 3 (gw.getD 0 0) (gl.getD 0 0), wordS IP 3 (gw.getD 1 0) (gl.getD 1 0),
        wordS IP 3 (gw.getD 2 0) (gl.getD 2 0), wordS IP 3 (gw.getD 3 0) (gl.getD 3 0),
        wordS IP 3 (gw.getD 4 0) (gl.getD 4 0)] p)
  | [], _ => by
    have e : embE6F4 K (CFSG.KC.F4Planes.pathE K gw gl []) = 1 := map_one (embE6F4 K)
    have h1 := hasBitsS_one (K := K)
    rw [← e] at h1
    exact h1
  | k :: p, h => by
    have hk : k < 5 := h k List.mem_cons_self
    have ih := hasBitsS_iota_pathE hI gw gl p fun j hj => h j (List.mem_cons_of_mem _ hj)
    have e : embE6F4 K (CFSG.KC.F4Planes.pathE K gw gl (k :: p)) =
        embE6F4 K (CFSG.KC.F4Planes.wordE K (gw.getD k 0) (gl.getD k 0)) *
          embE6F4 K (CFSG.KC.F4Planes.pathE K gw gl p) :=
      map_mul (embE6F4 K) (CFSG.KC.F4Planes.wordE K (gw.getD k 0) (gl.getD k 0))
        (CFSG.KC.F4Planes.pathE K gw gl p)
    have hw : ∀ W L, HasBitsS K (embE6F4 K (CFSG.KC.F4Planes.wordE K W L)) (wordS IP 3 W L) :=
      fun W L => by
        rw [iota_wordE]
        exact hasBitsS_wordS _ (fun c hc => hI c (by simpa using hc)) W L
    have hk' : HasBitsS K (embE6F4 K (CFSG.KC.F4Planes.wordE K (gw.getD k 0) (gl.getD k 0)))
        ([wordS IP 3 (gw.getD 0 0) (gl.getD 0 0), wordS IP 3 (gw.getD 1 0) (gl.getD 1 0),
          wordS IP 3 (gw.getD 2 0) (gl.getD 2 0), wordS IP 3 (gw.getD 3 0) (gl.getD 3 0),
          wordS IP 3 (gw.getD 4 0) (gl.getD 4 0)].getD k 0) := by
      interval_cases k
      all_goals simp only [List.getD_cons_zero, List.getD_cons_succ]
      all_goals exact hw _ _
    have hm := hk'.mul ih
    rw [← e] at hm
    exact hm

theorem pinE_sound {IP : ℕ} (hI : ∀ c < 8, HasBitsS K (iotaL K c) (letT IP c))
    {gw gl pS : List ℕ} {paths : List (List ℕ)} (h : pinE IP gw gl paths pS = true) {i : ℕ}
    (hi : i < 6) :
    HasBitsS K (embE6F4 K (CFSG.KC.F4Planes.pathE K gw gl (paths.getD i []))) (pS.getD i 0) := by
  simp only [pinE, strictB_eq6] at h
  have h' := allN_spec h i hi
  rw [Bool.and_eq_true] at h'
  have hp : ∀ k ∈ paths.getD i [], k < 5 := fun k hk => by
    simpa using allL_spec6 h'.1 k hk
  exact (hasBitsS_iota_pathE hI gw gl _ hp).of_eqS h'.2

theorem map_fS {G H : Type*} [Group G] [Group H] (f : G →* H) (s : Fin 4 → G) (a : ℕ) :
    f (CFSG.KC.F4Syl3.fS s a) = CFSG.KC.F4Syl3.fS (fun i => f (s i)) a := by
  simp only [CFSG.KC.F4Syl3.fS, CFSG.KC.F4Syl3.sE4, map_mul, map_pow]

theorem map_phi {G H : Type*} [Group G] [Group H] (f : G →* H) (s : Fin 4 → G) (g4 g5 : G)
    (m : ℕ) : f (CFSG.KC.F4Syl3.phi s g4 g5 m) =
      CFSG.KC.F4Syl3.phi (fun i => f (s i)) (f g4) (f g5) m := by
  simp only [CFSG.KC.F4Syl3.phi, CFSG.KC.F4Syl3.gQ, map_mul, map_pow, map_fS]

theorem hasBitsS_fSE {s : Fin 4 → adjointGroup Tag.E6 K} {S0 S1 S2 S3 : ℕ}
    (h0 : HasBitsS K (s 0) S0) (h1 : HasBitsS K (s 1) S1) (h2 : HasBitsS K (s 2) S2)
    (h3 : HasBitsS K (s 3) S3) (a : ℕ) :
    HasBitsS K (CFSG.KC.F4Syl3.fS s a) (fSE S0 S1 S2 S3 a) := by
  have e : CFSG.KC.F4Syl3.fS s a =
      s 0 ^ (a % 3) * s 1 ^ (a / 3 % 3) * s 2 ^ (a / 9 % 3) * s 3 ^ (a / 27 % 3) := by
    simp only [CFSG.KC.F4Syl3.fS, CFSG.KC.F4Syl3.sE4, CFSG.KC.F4Syl3.dg]
    norm_num
  rw [e]
  exact (((h0.pow _).mul (h1.pow _)).mul (h2.pow _)).mul (h3.pow _)

theorem hasBitsS_phiE {s : Fin 4 → adjointGroup Tag.E6 K} {g4 g5 : adjointGroup Tag.E6 K}
    {S0 S1 S2 S3 G4 G5 : ℕ} (h0 : HasBitsS K (s 0) S0) (h1 : HasBitsS K (s 1) S1)
    (h2 : HasBitsS K (s 2) S2) (h3 : HasBitsS K (s 3) S3) (h4 : HasBitsS K g4 G4)
    (h5 : HasBitsS K g5 G5) (m : ℕ) :
    HasBitsS K (CFSG.KC.F4Syl3.phi s g4 g5 m) (phiE S0 S1 S2 S3 G4 G5 m) := by
  have e : CFSG.KC.F4Syl3.phi s g4 g5 m =
      CFSG.KC.F4Syl3.fS s (m % 81) * (g4 ^ (m / 81 % 3) * g5 ^ (m / 243 % 3)) := by
    rw [CFSG.KC.F4Syl3.phi, CFSG.KC.F4Syl3.gQ, Nat.div_div_eq_div_mul]
  rw [e]
  exact (hasBitsS_fSE h0 h1 h2 h3 _).mul ((h4.pow _).mul (h5.pow _))

variable [Finite K]

theorem rowE_sound (hK : Nat.card K = 2) {LP IP IPi : ℕ} (hL : letOK LP = true)
    (hI : ∀ c < 8, HasBitsS K (iotaL K c) (letT IP c) ∧ HasBitsS K (iotaL K c)⁻¹ (letT IPi c))
    {pS : List ℕ} {ab ij : ℕ × ℕ} {gs : List G4} {tg : List (List ℕ)}
    {a b : adjointGroup Tag.F4 K}
    (ha : HasBitsS K (embE6F4 K a) (phiE (pS.getD 0 0) (pS.getD 1 0) (pS.getD 2 0)
      (pS.getD 3 0) (pS.getD 4 0) (pS.getD 5 0) ab.1))
    (hb : HasBitsS K (embE6F4 K b) (phiE (pS.getD 0 0) (pS.getD 1 0) (pS.getD 2 0)
      (pS.getD 3 0) (pS.getD 4 0) (pS.getD 5 0) ab.2))
    (h : rowE LP IP IPi pS ab ij gs tg = true) :
    ∃ e ∈ Subgroup.closure ({a, b} : Set (adjointGroup Tag.F4 K)), e ≠ 1 ∧
      Subgroup.closure (((embE6F4 K).range : Set (adjointGroup .E6 K)) ∪
        (Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) :
          Set (adjointGroup .E6 K))) = ⊤ := by
  simp only [rowE, strictB_eq6, Bool.and_eq_true, Bool.not_eq_true', lenL_eq6] at h
  obtain ⟨⟨hE1, hgs⟩, htg⟩ := h
  set e : adjointGroup Tag.F4 K := a ^ ij.1 * b ^ ij.2 with hedef
  have hE : HasBitsS K (embE6F4 K e) (mulS (powS (phiE (pS.getD 0 0) (pS.getD 1 0)
      (pS.getD 2 0) (pS.getD 3 0) (pS.getD 4 0) (pS.getD 5 0) ab.1) ij.1)
      (powS (phiE (pS.getD 0 0) (pS.getD 1 0) (pS.getD 2 0) (pS.getD 3 0) (pS.getD 4 0)
        (pS.getD 5 0) ab.2) ij.2)) := by
    rw [hedef, map_mul, map_pow, map_pow]
    exact (ha.pow _).mul (hb.pow _)
  have heA : a ∈ Subgroup.closure ({a, b} : Set (adjointGroup Tag.F4 K)) :=
    Subgroup.subset_closure (by simp)
  have heB : b ∈ Subgroup.closure ({a, b} : Set (adjointGroup Tag.F4 K)) :=
    Subgroup.subset_closure (by simp)
  refine ⟨e, mul_mem (pow_mem heA _) (pow_mem heB _), fun h1 => ?_, ?_⟩
  · rw [h1, map_one] at hE
    rw [(hE.eq_iff hasBitsS_one).1 rfl] at hE1
    exact Bool.noConfusion hE1
  set S := Subgroup.closure (((embE6F4 K).range : Set (adjointGroup .E6 K)) ∪
    (Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) :
      Set (adjointGroup .E6 K))) with hSdef
  have hmemI : ∀ x : adjointGroup Tag.F4 K, embE6F4 K x ∈ S := fun x =>
    Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
  have hcent : ∀ x ∈ Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)), x ∈ S :=
    fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hgen : ∀ g ∈ gs, ∃ w ∈ Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)),
      HasBitsS K w g.2.2.1 ∧ HasBitsS K w⁻¹ g.2.2.2 := by
    intro g hg
    have h' := allL_spec6 hgs g hg
    simp only [genE, strictB_eq6, Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    have hT := (hasBitsS_wordS_letters (K := K) hL g.1 g.2.1).of_eqS h1
    refine ⟨_, ?_, hT, hasBitsS_inv_of hT h2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hT.mul hE).eq_iff (hE.mul hT)).2 h3
  have htok : ∀ k, k < 16 + (gs.length + gs.length) →
      ∃ x ∈ S, HasBitsS K x (tokE IP IPi gs gs.length k) := by
    intro k hk
    by_cases h8 : k < 8
    · have hb8 : Nat.blt k 8 = true := blt_true h8
      have e1 : tokE IP IPi gs gs.length k = letT IP k := by
        rw [tokE, hb8]
      rw [e1]
      exact ⟨_, hmemI _, (hI k h8).1⟩
    have hb8 : Nat.blt k 8 = false := blt_false h8
    by_cases h8n : k < 8 + gs.length
    · have hb2 : Nat.blt k (Nat.add 8 gs.length) = true := blt_true h8n
      have hlt : k - 8 < gs.length := by omega
      have e1 : tokE IP IPi gs gs.length k = (gs.getD (k - 8) (0, 0, 0, 0)).2.2.1 := by
        rw [tokE, hb8, hb2]
        rfl
      rw [e1, List.getD_eq_getElem _ _ hlt]
      obtain ⟨w, hw, hT, -⟩ := hgen _ (List.getElem_mem hlt)
      exact ⟨w, hcent w hw, hT⟩
    have hb2 : Nat.blt k (Nat.add 8 gs.length) = false := blt_false h8n
    by_cases h16 : k < 16 + gs.length
    · have hb3 : Nat.blt k (Nat.add 16 gs.length) = true := blt_true h16
      have e1 : tokE IP IPi gs gs.length k = letT IPi (k - (8 + gs.length)) := by
        rw [tokE, hb8, hb2, hb3]
        rfl
      rw [e1]
      exact ⟨_, inv_mem (hmemI _), (hI _ (by omega)).2⟩
    have hb3 : Nat.blt k (Nat.add 16 gs.length) = false := blt_false h16
    have hlt : k - (16 + gs.length) < gs.length := by omega
    have e1 : tokE IP IPi gs gs.length k =
        (gs.getD (k - (16 + gs.length)) (0, 0, 0, 0)).2.2.2 := by
      rw [tokE, hb8, hb2, hb3]
      rfl
    rw [e1, List.getD_eq_getElem _ _ hlt]
    obtain ⟨w, hw, -, hY⟩ := hgen _ (List.getElem_mem hlt)
    exact ⟨w⁻¹, inv_mem (hcent w hw), hY⟩
  have hprod : ∀ idx : List ℕ, (∀ k ∈ idx, k < 16 + (gs.length + gs.length)) →
      ∃ x ∈ S, HasBitsS K x (prodE IP IPi gs gs.length idx) := by
    intro idx
    induction idx with
    | nil => exact fun _ => ⟨1, one_mem _, hasBitsS_one⟩
    | cons k idx ih =>
      intro hk
      obtain ⟨x, hx, hxb⟩ := htok k (hk k List.mem_cons_self)
      obtain ⟨y, hy, hyb⟩ := ih fun j hj => hk j (List.mem_cons_of_mem _ hj)
      exact ⟨x * y, mul_mem hx hy, hxb.mul hyb⟩
  have htarg : ∀ t < 4, E6Bits.evalG K ((decW 4 (tgW t) (tgL t)).map E6Salt.letterOfCode) ∈ S := by
    intro t ht
    have h' := allN_spec htg t ht
    simp only [tgtE, Bool.and_eq_true] at h'
    have hidx : ∀ k ∈ tg.getD t [], k < 16 + (gs.length + gs.length) := fun k hk =>
      lt_of_blt (allL_spec6 h'.1 k hk)
    obtain ⟨x, hx, hxb⟩ := hprod _ hidx
    rw [← (hxb.eq_iff (hasBitsS_wordS_letters (K := K) hL (tgW t) (tgL t))).2 h'.2]
    exact hx
  have hx0 : E6Bits.evalG K (wordOfCodes6 [0]) ∈ S := by
    have := htarg 0 (by decide)
    rwa [decW_tgW.1] at this
  have hx2 : E6Bits.evalG K (wordOfCodes6 [2]) ∈ S := by
    have := htarg 1 (by decide)
    rwa [decW_tgW.2.1] at this
  have hy0 : E6Bits.evalG K (wordOfCodes6 [0, 6 + 0, 0]) ∈ S := by
    have := htarg 2 (by decide)
    rwa [decW_tgW.2.2.1] at this
  have hy2 : E6Bits.evalG K (wordOfCodes6 [2, 6 + 2, 2]) ∈ S := by
    have := htarg 3 (by decide)
    rwa [decW_tgW.2.2.2] at this
  have hxI : ∀ j : Fin Tag.F4.rank,
      E6Bits.evalG K (wordOfCodes6 (orbitNodes j)) ∈ S := fun j => by
    have e1 : embE6F4 K (xE Tag.F4 K j 1) = E6Bits.evalG K (wordOfCodes6 (orbitNodes j)) :=
      Subtype.ext (iota_xE j)
    rw [← e1]
    exact hmemI _
  have hyI : ∀ j : Fin Tag.F4.rank, E6Bits.evalG K
      (wordOfCodes6 ((orbitNodes j).flatMap fun i => [i, 6 + i, i])) ∈ S := fun j => by
    have e1 : embE6F4 K (yE Tag.F4 K j 1) =
        E6Bits.evalG K (wordOfCodes6 ((orbitNodes j).flatMap fun i => [i, 6 + i, i])) :=
      Subtype.ext (iota_yE j)
    rw [← e1]
    exact hmemI _
  have hX : ∀ i < 6, E6Bits.evalG K (wordOfCodes6 [i]) ∈ S := by
    intro i hi
    interval_cases i
    · exact hx0
    · exact hxI ⟨0, by decide⟩
    · exact hx2
    · exact hxI ⟨1, by decide⟩
    · have h1 := hxI ⟨2, by decide⟩
      have e1 : wordOfCodes6 (orbitNodes (⟨2, by decide⟩ : Fin Tag.F4.rank)) =
          wordOfCodes6 [2] ++ wordOfCodes6 [4] := rfl
      rw [e1, E6Bits.evalG_append] at h1
      exact (S.mul_mem_cancel_left hx2).1 h1
    · have h1 := hxI ⟨3, by decide⟩
      have e1 : wordOfCodes6 (orbitNodes (⟨3, by decide⟩ : Fin Tag.F4.rank)) =
          wordOfCodes6 [0] ++ wordOfCodes6 [5] := rfl
      rw [e1, E6Bits.evalG_append] at h1
      exact (S.mul_mem_cancel_left hx0).1 h1
  have hY : ∀ i < 6, E6Bits.evalG K (wordOfCodes6 [i, 6 + i, i]) ∈ S := by
    intro i hi
    interval_cases i
    · exact hy0
    · exact hyI ⟨0, by decide⟩
    · exact hy2
    · exact hyI ⟨1, by decide⟩
    · have h1 := hyI ⟨2, by decide⟩
      have e1 : wordOfCodes6 ((orbitNodes (⟨2, by decide⟩ : Fin Tag.F4.rank)).flatMap
          fun i => [i, 6 + i, i]) = wordOfCodes6 [2, 6 + 2, 2] ++ wordOfCodes6 [4, 6 + 4, 4] :=
        rfl
      rw [e1, E6Bits.evalG_append] at h1
      exact (S.mul_mem_cancel_left hy2).1 h1
    · have h1 := hyI ⟨3, by decide⟩
      have e1 : wordOfCodes6 ((orbitNodes (⟨3, by decide⟩ : Fin Tag.F4.rank)).flatMap
          fun i => [i, 6 + i, i]) = wordOfCodes6 [0, 6 + 0, 0] ++ wordOfCodes6 [5, 6 + 5, 5] :=
        rfl
      rw [e1, E6Bits.evalG_append] at h1
      exact (S.mul_mem_cancel_left hy0).1 h1
  rw [eq_top_iff, ← closure_xElement_yElement (τ := Tag.E6) (K := K), Subgroup.closure_le]
  rintro _ ⟨i, c', rfl | rfl⟩
  · rcases CFSG.LieType.Simplicity.TitsBits.eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · rw [xElement_zero]
      exact one_mem _
    · have := hX i.val (by have := i.2; simp only [Tag.rank] at this; omega)
      rwa [evalG6_x] at this
  · rcases CFSG.LieType.Simplicity.TitsBits.eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · have e0 : yElement (τ := Tag.E6) (K := K) i 0 = 1 := Subtype.ext (Units.ext (yOp_zero i))
      rw [e0]
      exact one_mem _
    · have := hY i.val (by have := i.2; simp only [Tag.rank] at this; omega)
      rwa [evalG6_xnx] at this

theorem rowAt_sound (hK : Nat.card K = 2) {LP IP IPi : ℕ} (hL : letOK LP = true)
    (hI : ∀ c < 8, HasBitsS K (iotaL K c) (letT IP c) ∧ HasBitsS K (iotaL K c)⁻¹ (letT IPi c))
    {s : Fin 4 → adjointGroup Tag.F4 K} {g4 g5 : adjointGroup Tag.F4 K} {pS : List ℕ}
    (hs : ∀ i : Fin 4, HasBitsS K (embE6F4 K (s i)) (pS.getD i 0))
    (h4 : HasBitsS K (embE6F4 K g4) (pS.getD 4 0)) (h5 : HasBitsS K (embE6F4 K g5) (pS.getD 5 0))
    {PR r : ℕ} {ij : List (ℕ × ℕ)} {gens : List (List G4)} {tgs : List (List (List ℕ))}
    (h : rowAt LP IP IPi pS PR ij gens tgs r = true) :
    ∃ e ∈ CFSG.KC.F4Planes.planeR s g4 g5 PR r, e ≠ 1 ∧
      Subgroup.closure (((embE6F4 K).range : Set (adjointGroup .E6 K)) ∪
        (Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) :
          Set (adjointGroup .E6 K))) = ⊤ := by
  have hphi : ∀ m, HasBitsS K (embE6F4 K (CFSG.KC.F4Syl3.phi s g4 g5 m))
      (phiE (pS.getD 0 0) (pS.getD 1 0) (pS.getD 2 0) (pS.getD 3 0) (pS.getD 4 0)
        (pS.getD 5 0) m) := fun m => by
    rw [map_phi]
    exact hasBitsS_phiE (hs 0) (hs 1) (hs 2) (hs 3) h4 h5 m
  have h' : rowE LP IP IPi pS (CFSG.KC.F4Planes.aR PR r, CFSG.KC.F4Planes.bR PR r)
      (ij.getD r (0, 0)) (gens.getD r []) (tgs.getD r []) = true := h
  exact rowE_sound (ab := (CFSG.KC.F4Planes.aR PR r, CFSG.KC.F4Planes.bR PR r)) hK hL hI
    (hphi _) (hphi _) h'

end Sound

end CFSG.KC.F4PlanesE6

end

module

public import Certificates.Data.Kernel.HJ12Orb
public import CFSG.Certificates.Kernel.HJ12KTSound

public section

namespace Certificates.Kernel.HJ12K

open CFSG.KC.Mat12P CFSG.KC.Mat8P CFSG.Quasithin.H13.MatNCert CFSG.GammaU.Native
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

theorem eraseDups_of_nodup : ∀ (l : List ℕ), l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.eraseDups_cons, List.filter_eq_self.2 ?_, eraseDups_of_nodup l h.2]
    intro b hb
    rw [Bool.not_eq_true', beq_eq_false_iff_ne]
    rintro rfl
    exact h.1 hb

theorem eraseDups_length {l : List ℕ} {n : ℕ} (h1 : nodupP l = true) (h2 : Nat.beq l.length n = true) :
    (l.eraseDups.length == n) = true := by
  rw [eraseDups_of_nodup l ((nodupP_iff l).1 h1), nat_beq]
  exact h2

theorem closedOrbit_eq (O : List ℕ) : closedOrbit O gensL = closedOQ O (maskOf 0 O) := by
  simp only [closedOrbit, closedOQ, gensL, List.all_cons, List.all_nil, Bool.and_true,
    Std.HashSet.contains_ofList, appN_hjAc, appN_hjBc, contains_bitQ]

theorem orbit_sound (O1 O2 : List ℕ) (h1 : orbitOf gensL 4 = O1) (h2 : orbitOf gensL 1024 = O2)
    (h : orbAt O1 O2 (maskOf 0 O1) (maskOf 0 O2) = true) : hjOrbitCheck = true := by
  simp only [orbAt, Bool.and_eq_true, and_assoc] at h
  obtain ⟨c1, c2, n1, l1, n2, l2, hp⟩ := h
  simp only [hjOrbitCheck, Bool.and_eq_true, and_assoc]
  rw [h1, h2, closedOrbit_eq, closedOrbit_eq]
  refine ⟨c1, c2, eraseDups_length n1 l1, eraseDups_length n2 l2, ?_⟩
  simp only [contains_bitQ, nat_beq]
  exact hp

theorem hjOrbitCheck_of (h : orbQ = true) : hjOrbitCheck = true := by
  rw [orbQ] at h
  exact orbit_sound _ _ (orbitOf_eq 4) (orbitOf_eq 1024) h

theorem inv_of_gensOKQ {gs : List ℕ} (h : gensOKQ gs = true) {s : ℕ} (hs : s ∈ gs) :
    invR (unpackA s) = unpackA (invQ s) :=
  invR_unpackA (List.all_eq_true.1 h s hs)

theorem s1_sound (gs ja X J : List ℕ) (egs : hj_stab1Words.map wordR = gs.map unpackA)
    (eja : (hj_a1Words ++ hj_a2Words).map wordR = ja.map unpackA)
    (EX : enumGrp (gs.map unpackA) = X.map unpackA) (EJ : enumGrp (ja.map unpackA) = J.map unpackA)
    (BX : ∀ q ∈ X, q < 2 ^ 144) (BJ : ∀ q ∈ J, q < 2 ^ 144) (h : s1At gs ja X J = true) :
    hjS1Check = true := by
  simp only [s1At, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [hjS1Check, Bool.and_eq_true, and_assoc]
  rw [egs, eja, EX, EJ]
  refine ⟨gensOKN_of _ h1, (closedCheck_eq _ _ BX).trans h2,
    (congrArg (· == 384) (dedup_length BX h3)).trans ((nat_beq _ _).trans h4),
    ?_, gensOKN_of _ h6, (closedCheck_eq _ _ BJ).trans h7, ?_, ?_⟩
  · exact (all_map_congr fun g _ => by rw [appN_unpackA, nat_beq]).trans h5
  · exact (congrArg (· == 64) (dedup_length BJ h8)).trans ((nat_beq _ _).trans h9)
  · refine (all_map_congr fun s hs => ?_).trans h10
    refine all_map_congr fun j _ => ?_
    rw [inv_of_gensOKQ h1 hs, mulR_unpackA, mulR_unpackA, contains_map BJ (mulQ_lt _ _)]

theorem hjS1Check_of (h : s1Q = true) : hjS1Check = true := by
  rw [s1Q, s1gQ, jaQ] at h
  obtain ⟨EX, BX⟩ := enumGrp_eq (hj_stab1Words.map wordQ)
  obtain ⟨EJ, BJ⟩ := enumGrp_eq ((hj_a1Words ++ hj_a2Words).map wordQ)
  exact s1_sound _ _ _ _ (words_eq _) (words_eq _) EX EJ BX BJ h

theorem getD1_map (ks : List ℕ) (d : ℕ) :
    (ks.map unpackA).getD 1 (unpackA d) = unpackA (ks.getD 1 d) := by
  rcases ks with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rfl

theorem s2_sound (es ks E K EK : List ℕ) (ees : hj_eWords.map wordR = es.map unpackA)
    (eks : hj_stWords.map wordR = ks.map unpackA)
    (EE : enumGrp (es.map unpackA) = E.map unpackA) (EK0 : enumGrp (ks.map unpackA) = K.map unpackA)
    (EEK : enumGrp ((es ++ ks).map unpackA) = EK.map unpackA)
    (BE : ∀ q ∈ E, q < 2 ^ 144) (BK : ∀ q ∈ K, q < 2 ^ 144) (BEK : ∀ q ∈ EK, q < 2 ^ 144)
    (h : s2At es ks E K EK = true) : hjS2Check = true := by
  simp only [s2At, ord5Q, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  simp only [hjS2Check, Bool.and_eq_true, and_assoc]
  rw [ees, eks, ← List.map_append, EE, EK0, EEK, idR_eq, List.headD_map, getD1_map]
  refine ⟨gensOKN_of _ h1, (closedCheck_eq _ _ BE).trans h2, (closedCheck_eq _ _ BK).trans h3,
    (closedCheck_eq _ _ BEK).trans h4,
    (congrArg (· == 4) (dedup_length BE h5)).trans ((nat_beq _ _).trans h6),
    (congrArg (· == 60) (dedup_length BK h7)).trans ((nat_beq _ _).trans h8),
    (congrArg (· == 240) (dedup_length BEK h9)).trans ((nat_beq _ _).trans h10), ?_,
    (all_map_congr fun x _ => all_map_congr fun y _ => commR_unpackA x y).trans h12, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · refine (all_map_congr fun x _ => ?_).trans h11
    rw [mulR_unpackA, beq_unpackA (mulQ_lt _ _) oneQ_lt, nat_beq]
  · rw [mulR_unpackA, beq_unpackA (mulQ_lt _ _) oneQ_lt, nat_beq]
    exact h13
  · rw [mulR_unpackA, mulR_unpackA, beq_unpackA (mulQ_lt _ _) oneQ_lt, nat_beq]
    exact h14
  · rw [mulR_unpackA, mulR_unpackA, mulR_unpackA, mulR_unpackA,
      beq_unpackA (mulQ_lt _ _) oneQ_lt, nat_beq]
    exact h15
  · exact (all_map_congr fun g _ => by rw [appN_unpackA, nat_beq]).trans h16
  · exact (all_map_congr fun e _ => all_map_congr fun k _ => commR_unpackA e k).trans h17
  · refine (all_map_congr fun x hx => ?_).trans h18
    rw [beq_unpackA (BE x hx) oneQ_lt, contains_map BK (BE x hx), nat_beq]

theorem hjS2Check_of (h : s2Q = true) : hjS2Check = true := by
  rw [s2Q, esQ, ksQ] at h
  obtain ⟨EE, BE⟩ := enumGrp_eq (hj_eWords.map wordQ)
  obtain ⟨EK0, BK⟩ := enumGrp_eq (hj_stWords.map wordQ)
  obtain ⟨EEK, BEK⟩ := enumGrp_eq (hj_eWords.map wordQ ++ hj_stWords.map wordQ)
  exact s2_sound _ _ _ _ _ (words_eq _) (words_eq _) EE EK0 EEK BE BK BEK h

theorem gam_sound (aw : List (List ℕ)) (bw xw : List ℕ) (g : ℕ) (gs A O : List ℕ)
    (egs : aw.map wordR = gs.map unpackA) (EA : enumGrp (gs.map unpackA) = A.map unpackA)
    (BA : ∀ q ∈ A, q < 2 ^ 144) (hO : orbitOf gensL 1024 = O)
    (h : gamAt gs A (wordQ bw) g (wordQ xw) O = true) : gammaOK aw bw g xw = true := by
  simp only [gamAt, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [gammaOK, Bool.and_eq_true, and_assoc]
  rw [egs, EA, wordR_eq bw, wordR_eq xw, hO, idR_eq]
  refine ⟨gensOKN_of _ h1, (closedCheck_eq _ _ BA).trans h2,
    (contains_map BA (wordQ_lt bw)).trans h3, ?_, ?_, (contains_map BA (wordQ_lt xw)).trans h6, ?_⟩
  · rw [bne, beq_unpackA (wordQ_lt _) oneQ_lt, nat_beq]
    exact h4
  · rw [appN_unpackA, nat_beq]
    exact h5
  · rw [appN_unpackA]
    exact h7

theorem hjGammaCheck_of (h : gamQ = true) : hjGammaCheck = true := by
  rw [gamQ, gam2, Bool.and_eq_true] at h
  rw [hjGammaCheck, Bool.and_eq_true]
  exact ⟨gam_sound _ _ _ _ _ _ _ (words_eq _) (enumGrp_eq _).1 (enumGrp_eq _).2 (orbitOf_eq 1024)
      h.1,
    gam_sound _ _ _ _ _ _ _ (words_eq _) (enumGrp_eq _).1 (enumGrp_eq _).2 (orbitOf_eq 1024) h.2⟩

end Certificates.Kernel.HJ12K

end

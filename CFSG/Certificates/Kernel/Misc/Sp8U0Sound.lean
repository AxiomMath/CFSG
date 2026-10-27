module

public import Certificates.Data.Kernel.Misc.Sp8U0
public import Certificates.Data.RudvalisFF81Sp8Sylow2
public import CFSG.Certificates.Kernel.Misc.BfsKWSound
public import CFSG.Certificates.Kernel.Misc.Sp8CzSound

public section

namespace CFSG.KC.Sp8U0

open CFSG.KD.Sp8U0 CFSG.KD.BfsK CFSG.KD.BfsKW CFSG.KC.BfsK CFSG.KC.BfsKW CFSG.KC.Mat8P
  CFSG.KC.Sp8Syl3 CFSG.KD.Sp8Syl3 CFSG.KD.Sp8Cz CFSG.KC.Sp8Cz CFSG.Quasithin.H13.Mat8Cert
  CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

variable {R : ℕ → ℕ}

theorem u0gen_enc (hz : ∀ s < 5, EncS (u0Gens.getD s []) (R s)) {s : ℕ} (hs : s < 5)
    (d : List ℕ) : EncS (u0Gens.getD s d) (R s) := by
  have hl : u0Gens.length = 5 := rfl
  rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hl]; exact hs) d []]
  exact hz s hs

theorem u0Tab_facts (hz : ∀ s < 5, EncS (u0Gens.getD s []) (R s)) (h : u0TabK R 65536 = true) :
    (tabS u0Gens 65536).size = 65536 ∧ closedCheck mulS u0Gens (tabS u0Gens 65536) = true ∧
      distinctCheck (tabS u0Gens 65536) = true ∧
      ∀ t < 65536, EncS ((tabS u0Gens 65536).getD t []) (recX R 9 t) := by
  unfold u0TabK at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, h⟩ := h
  exact tableKW_ok (ok := validS) (num := code64) code_inj
    (start := one8) (mul := mulS) (gens := u0Gens) (fuel := 65536) (k := 5) rfl (by norm_num)
    (by norm_num) le_rfl (fun x N hx s hs d => mulE hx (u0gen_enc hz hs d))
    (by rw [h0]; exact one_enc) h (by norm_num) (by norm_num) (by norm_num)

theorem u0Chk_of (hz : ∀ s < 5, EncS (u0Gens.getD s []) (R s)) (hsp : u0Gens.all spS = true)
    (h : u0TabK R 65536 = true) : u0Chk899106 = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := u0Tab_facts hz h
  unfold u0Chk899106 tabOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨hsz, hcl⟩, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => ?_⟩, hsp⟩
  rw [hsz] at ht
  exact (hrec t ht).1

theorem zuChk_of (hz : ∀ s < 5, EncS (u0Gens.getD s []) (R s))
    (hzu : List.Forall₂ EncS zuS [R 5, R 6, R 7, R 8]) (h : u0TabK R 65536 = true)
    (hk : zuK R = true)
    (hfix : ((zuS.map fun z => (fixS z, aTypeS z)) ==
      [(256, true), (64, true), (128, false), (64, false)]) = true) :
    zuChk899106 = true := by
  obtain ⟨hsz, -, -, hrec⟩ := u0Tab_facts hz h
  have hall := CFSG.KC.G2Three.allBelow_g2 hk (by norm_num)
  have g0 : EncS [1, 3, 4, 8, 48, 32, 64, 128] (R 0) := hz 0 (by norm_num)
  have g1 : EncS [1, 2, 6, 8, 16, 96, 64, 128] (R 1) := hz 1 (by norm_num)
  have g2 : EncS [1, 2, 4, 12, 16, 32, 192, 128] (R 2) := hz 2 (by norm_num)
  have g3 : EncS [1, 2, 4, 8, 16, 32, 68, 128] (R 3) := hz 3 (by norm_num)
  have g4 : EncS [1, 2, 4, 8, 16, 32, 64, 136] (R 4) := hz 4 (by norm_num)
  unfold zuChk899106
  rw [hfix, Bool.and_true]
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hsz] at ht
  have hx := hrec t ht
  have e := hall t ht
  generalize (tabS u0Gens 65536).getD t [] = x at hx ⊢
  simp only [u0Gens, List.all_cons, List.all_nil, Bool.and_true]
  rw [commS_eq hx g0, commS_eq hx g1, commS_eq hx g2, commS_eq hx g3, commS_eq hx g4,
    contains_eq hzu hx]
  exact e

end CFSG.KC.Sp8U0

end

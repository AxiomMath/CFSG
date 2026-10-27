module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBI2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

@[expose] def fzbSix (c : Bool) : List ℕ :=
  [128, fzbMul c 128 1, 832, fzbMul c 832 1, fzbMul c 128 832, fzbMul c (fzbMul c 128 832) 1]

theorem fzb_model_pigeon {c : Bool} (hF : FzbFacts c) {ψ : ℕ → ℕ} (hψ : FzbIsEmb c 832 ψ)
    (hcomm : ∀ e ∈ fzbSix c, fzbMul c e 832 = fzbMul c 832 e)
    (hnz : ∀ e ∈ fzbSix c, 4 ≤ ψ e) : False := by
  have h1c : fzbMul c 1 832 = fzbMul c 832 1 := hF.comm_z_u
  have ht1c : fzbMul c 128 832 = fzbMul c 832 128 := hF.comm_t_u
  have h1lt : ψ 1 < 1024 := hψ.lt 1 (by norm_num) h1c
  have h128lt : ψ 128 < 1024 := hψ.lt 128 (by norm_num) ht1c
  have hH2 := hF.H2 ψ hψ
  have hW1 : fzbW0 (ψ 1) := hH2.1
  have hW128 : fzbW0 (ψ 128) := hH2.2
  have hlt : ∀ e ∈ fzbSix c, e < 1024 := by
    intro e he
    simp only [fzbSix, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · exact hF.mul_lt 128 (by norm_num) 1 (by norm_num)
    · norm_num
    · exact hF.mul_lt 832 (by norm_num) 1 (by norm_num)
    · exact hF.mul_lt 128 (by norm_num) 832 (by norm_num)
    · exact hF.mul_lt (fzbMul c 128 832) (hF.mul_lt 128 (by norm_num) 832 (by norm_num))
        1 (by norm_num)
  have he5mem : fzbMul c 128 832 ∈ fzbSix c := by
    simp only [fzbSix, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have he5lt : fzbMul c 128 832 < 1024 := hlt _ he5mem
  have he5comm : fzbMul c (fzbMul c 128 832) 832 = fzbMul c 832 (fzbMul c 128 832) :=
    hcomm _ he5mem
  have hW5 : fzbW0 (ψ (fzbMul c 128 832)) := by
    rw [hψ.map_mul 128 (by norm_num) 832 (by norm_num) ht1c rfl, hψ.map_u]
    exact hF.W0_mul (ψ 128) h128lt hW128 128 (by norm_num) (by norm_num [fzbW0])
  have hW6 : fzbW0 (ψ (fzbMul c (fzbMul c 128 832) 1)) := by
    rw [hψ.map_mul (fzbMul c 128 832) he5lt 1 (by norm_num) he5comm h1c]
    exact hF.W0_mul (ψ (fzbMul c 128 832)) (hψ.lt _ he5lt he5comm) hW5 (ψ 1) h1lt hW1
  have hW0 : ∀ e ∈ fzbSix c, fzbW0 (ψ e) := by
    intro e he
    simp only [fzbSix, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hW128
    · rw [hψ.map_mul 128 (by norm_num) 1 (by norm_num) ht1c h1c]
      exact hF.W0_mul (ψ 128) h128lt hW128 (ψ 1) h1lt hW1
    · rw [hψ.map_u]
      norm_num [fzbW0]
    · rw [hψ.map_mul 832 (by norm_num) 1 (by norm_num) rfl h1c, hψ.map_u]
      exact hF.W0_mul 128 (by norm_num) (by norm_num [fzbW0]) (ψ 1) h1lt hW1
    · exact hW5
    · exact hW6
  have hnodup : (fzbSix c).Nodup := by unfold fzbSix; exact hF.nodup
  have hmapnodup : ((fzbSix c).map ψ).Nodup :=
    hnodup.map_on fun a ha b hb h =>
      hψ.inj a (hlt a ha) b (hlt b hb) (hcomm a ha) (hcomm b hb) h
  have hcard : ((fzbSix c).map ψ).toFinset.card = 6 := by
    rw [List.toFinset_card_of_nodup hmapnodup]
    simp [fzbSix]
  have hsub : ((fzbSix c).map ψ).toFinset ⊆ Finset.Icc 128 131 := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have h4 := hnz e he
    have hw := hW0 e he
    simp only [Finset.mem_Icc]
    unfold fzbW0 at hw
    rcases hw with h | ⟨h1, h2⟩
    · omega
    · exact ⟨h1, by omega⟩
  have hle : ((fzbSix c).map ψ).toFinset.card ≤ (Finset.Icc 128 131).card :=
    Finset.card_le_card hsub
  have h4card : (Finset.Icc 128 131).card = 4 := by simp
  rw [h4card] at hle
  omega

end CFSG.OddStandard.SmallF3.FritzII

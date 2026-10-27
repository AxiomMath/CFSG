module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelOrbitBits
public import CFSG.Quasithin.Background.HZCoc24B

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLzMasks

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc24
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelOrbitBits

@[expose] def latX : List ℕ := [492, 292, 212, 1562, 1561, 703, 1375, 1824, 991, 1471, 1728]

@[expose] def latY : List ℕ := [1547, 1563, 1926, 1637, 492, 864, 1440, 960, 1248, 159, 287]

theorem latX_eq : latX = matOf 11 (act11 lzXArr) := by decide +kernel

theorem latY_eq : latY = matOf 11 (act11 lzYArr) := by decide +kernel

theorem actM_latX {m : ℕ} (hm : m < 2 ^ 11) : actM latX m = lzAct 0 m := by
  rw [latX_eq, actM_matOf (xorLin_act11 lzXArr) 11 m hm]
  simp [lzAct]

theorem actM_latY {m : ℕ} (hm : m < 2 ^ 11) : actM latY m = lzAct 1 m := by
  rw [latY_eq, actM_matOf (xorLin_act11 lzYArr) 11 m hm]
  simp [lzAct]

theorem exists_img11_Lz_actM {c : List ℕ} (hc : c ∈ [latX, latY]) {m : ℕ} (hm : m < 2 ^ 11) :
    ∃ x ∈ img11 Lz, x (toW 11 m) = toW 11 (actM c m) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rw [actM_latX hm]
    exact rho_lzAct 0 m
  · rw [actM_latY hm]
    exact rho_lzAct 1 m

theorem actM_lt_of_mem {c : List ℕ} (hc : c ∈ [latX, latY]) (m : ℕ) : actM c m < 2 ^ 11 := by
  refine actM_lt (fun d hd => ?_) m
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simp only [latX, List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  · simp only [latY, List.mem_cons, List.not_mem_nil, or_false] at hd
    omega

theorem orbitBits_lz_spec (P : ℕ → Prop)
    (hP : ∀ m < 2 ^ 11, P m → ∀ x ∈ img11 Lz, ∀ k, x (toW 11 m) = toW 11 k → k < 2 ^ 11 → P k)
    {r : ℕ} (hr : r < 2 ^ 11) (hPr : P r) :
    ∀ n, (orbitBits [latX, latY] 2048 [r] (1 <<< r)).testBit n = true → n < 2 ^ 11 ∧ P n := by
  refine orbitBits_root_spec [latX, latY] (fun m => m < 2 ^ 11 ∧ P m) ?_ r ⟨hr, hPr⟩ 2048
  rintro c hc m ⟨hm, hPm⟩
  obtain ⟨x, hx, hxe⟩ := exists_img11_Lz_actM hc hm
  have hlt := actM_lt_of_mem hc m
  exact ⟨hlt, hP m hm hPm x hx _ hxe hlt⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLzMasks

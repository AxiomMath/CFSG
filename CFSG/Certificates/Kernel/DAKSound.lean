module

public import CFSG.Certificates.Kernel.TWDKSound
public import Certificates.Data.Kernel.DAK
public import CFSG.LocalAnalysis.StandardType.GGDepASmallNat

public section

namespace CFSG.StandardType.DAK

open Certificates.DAK Certificates.TWDK Certificates.DepASmall
open CFSG.StandardType CFSG.StandardType.TWDK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ}

theorem dak_of_cover {F : List GGDepANPair} {S : List KSingleE} (hC : dakCover N S = true)
    (hS : ∀ i < S.length, dakSingleAt p N F S i = true) (b c0 mi ni : ℕ) (hb : b < N - 1)
    (hc0 : c0 < N - 1) (hmi : mi = 1 ∨ mi = 2) (hni : ni = 1 ∨ ni = 2)
    (hpat : ggDepANPatB N b c0 mi ni = true) :
    ∃ wits idx, dakSingle p N F (b, c0, mi, ni) wits idx = true := by
  have h1 := List.all_eq_true.mp hC b (List.mem_range.mpr hb)
  have h2 := List.all_eq_true.mp h1 c0 (List.mem_range.mpr hc0)
  have h3 := List.all_eq_true.mp h2 mi (by rcases hmi with rfl | rfl <;> simp)
  have h4 := List.all_eq_true.mp h3 ni (by rcases hni with rfl | rfl <;> simp)
  have h5 : (b, c0, mi, ni) ∈ S.map (·.1) := by simpa [hpat] using h4
  obtain ⟨e, he, hek⟩ := List.mem_map.mp h5
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have h6 := hS i hi
  simp only [dakSingleAt, List.getElem?_eq_getElem hi] at h6
  rw [hek] at h6
  exact ⟨_, _, h6⟩

theorem dakPat_wit (b c0 : Fin (N - 1)) {m n : ℤ} (h : GGDepAPat N b c0 m n) :
    ∃ mi ni : ℕ, (mi = 1 ∨ mi = 2) ∧ (ni = 1 ∨ ni = 2) ∧
      m = -(mi : ℤ) ∧ n = -(ni : ℤ) ∧ ggDepANPatB N b.val c0.val mi ni = true := by
  have h' := h
  unfold GGDepAPat at h'
  obtain ⟨-, -, h'⟩ := h'
  have hmn : (m = -1 ∧ n = -1) ∨ (m = -1 ∧ n = -2) ∨ (m = -2 ∧ n = -1) := by
    rcases h' with ⟨-, hmn⟩ | ⟨-, -, hm, hn⟩ | ⟨-, -, hm, hn⟩
    · exact hmn
    · exact Or.inl ⟨hm, hn⟩
    · exact Or.inl ⟨hm, hn⟩
  rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, rfl, rfl,
      (ggDepANPatB_iff b c0 1 1 (Or.inl rfl) (Or.inl rfl)).mpr h⟩
  · exact ⟨1, 2, Or.inl rfl, Or.inr rfl, rfl, rfl,
      (ggDepANPatB_iff b c0 1 2 (Or.inl rfl) (Or.inr rfl)).mpr h⟩
  · exact ⟨2, 1, Or.inr rfl, Or.inl rfl, rfl, rfl,
      (ggDepANPatB_iff b c0 2 1 (Or.inr rfl) (Or.inl rfl)).mpr h⟩

theorem aaParam_getD_lt (hp : 0 < p) (b c0 m u v j : ℕ) :
    (ggDepANAaParam p N b c0 m u v).getD j 0 < p := by
  rw [ggDepANAaParam, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hj : j < N
  · rw [List.getElem?_range hj, Option.map_some, Option.getD_some]
    split_ifs <;> exact Nat.mod_lt _ hp
  · rw [List.getElem?_eq_none (by simpa using hj), Option.map_none, Option.getD_none]
    exact hp

theorem mem_dakCells {b c0 mi ni s t u : ℕ} (hs : s < p) (ht : t < p) (hu : u < p)
    (h0 : (ggDepANAaParam p N b c0 ((p - mi) % p) u 1).getD 0 0 = 0)
    (hd : ggDepANDot p (ggDepANAaParam p N b c0 ((p - mi) % p) u 1)
      (ggDepANHaParam p N b c0 ((p - ni) % p) s t) = 2 % p) :
    (ggDepANHaParam p N b c0 ((p - ni) % p) s t, ggDepANAaParam p N b c0 ((p - mi) % p) u 1) ∈
      dakCells p N b c0 mi ni := by
  unfold dakCells
  refine List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu, ?_⟩
  try dsimp only
  rw [if_pos (beq_iff_eq.mpr h0)]
  refine List.mem_flatMap.mpr ⟨s, List.mem_range.mpr hs, ?_⟩
  refine List.mem_filterMap.mpr ⟨t, List.mem_range.mpr ht, ?_⟩
  try dsimp only
  rw [if_pos (beq_iff_eq.mpr hd)]

theorem dak_cells [Fact p.Prime] (hp : 5 ≤ p) (hpN : p ∣ N) (hN : 5 ≤ N)
    (F : List GGDepANPair) (S : List KSingleE) (hF : kFrameOK p N F = true)
    (hC : dakCover N S = true) (hS : ∀ i < S.length, dakSingleAt p N F S i = true) :
    GGDepASmallCells p N := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro b c0 m n hpat ha αa hpairs hdot2 hx
  have hpat' := hpat
  unfold GGDepAPat at hpat'
  obtain ⟨hb, hbc, -⟩ := hpat'
  obtain ⟨mi, ni, hmi, hni, hm, hn, hpatB⟩ := dakPat_wit b c0 hpat
  obtain ⟨wits, idx, hchk⟩ := dak_of_cover hC hS b.val c0.val mi ni b.isLt c0.isLt hmi hni hpatB
  rw [twDot_x (N := N) (by omega)] at hx
  obtain ⟨e, d, hed, hde, hfr, hdh, hea, -, α', hα', hα0, hα1⟩ := twNorm hpN hN αa hx
  have hm_cast : (m : ZMod p) = (((p - mi) % p : ℕ) : ZMod p) := by
    rw [hm, Int.cast_neg, Int.cast_natCast]
    exact (l05nND_cast_neg p mi (by rcases hmi with rfl | rfl <;> omega)).symm
  have hn_cast : (n : ZMod p) = (((p - ni) % p : ℕ) : ZMod p) := by
    rw [hn, Int.cast_neg, Int.cast_natCast]
    exact (l05nND_cast_neg p ni (by rcases hni with rfl | rfl <;> omega)).symm
  have hpairA : ∀ c : Fin (N - 1), c ≠ b →
      ggDepAdot α' (ggDepAh p N c) = if c = c0 then (((p - mi) % p : ℕ) : ZMod p) else 0 := by
    intro c hc
    rw [hα', hdh, (hpairs c hc).1, hm_cast]
  obtain ⟨u, v, huv⟩ := ggDepANAa_complete hpN hN b c0 hb hbc ((p - mi) % p) α' hpairA
  have hpairH : ∀ c : Fin (N - 1), c ≠ b →
      ggDepAdot (ggDepAα p N c) (e ha) = if c = c0 then (((p - ni) % p : ℕ) : ZMod p) else 0 := by
    intro c hc
    rw [hea, (hpairs c hc).2, hn_cast]
  obtain ⟨s, t, hst⟩ := ggDepANHa_complete hN b c0 hb hbc ((p - ni) % p) (e ha) hpairH
  have hp0 : 0 < p := by omega
  have hv1 : v % p = 1 := by
    have h1 := hα1
    rw [vAt_lt _ (by omega : N - 1 < N), huv] at h1
    change (((ggDepANAaParam p N b.val c0.val ((p - mi) % p) u v).getD (N - 1) 0 : ℕ) : ZMod p) = 1
      at h1
    rw [l05nND_AaParam_getD _ _ _ _ _ _ _ (by omega)] at h1
    exact twNat_eq (Nat.mod_lt _ hp0) (by omega : 1 < p) (by rw [h1, Nat.cast_one])
  have hAeq : ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) 1 =
      ggDepANAaParam p N b.val c0.val ((p - mi) % p) u v := by
    have h := l05nND_AaParam_mod p N b.val c0.val ((p - mi) % p) u v
    rw [hv1] at h
    exact h
  have hA : ggDepANToZ p N (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) 1) = α' := by
    rw [hAeq]
    exact huv.symm
  have hH : ggDepANToZ p N (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p)) =
      e ha := by
    rw [l05nND_HaParam_mod]
    exact hst.symm
  have h0 : (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) 1).getD 0 0 = 0 := by
    have h1 := hα0
    rw [vAt_lt _ (by omega : 0 < N), ← hA] at h1
    change (((ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) 1).getD 0 0 : ℕ) :
      ZMod p) = 0 at h1
    exact twNat_eq (aaParam_getD_lt hp0 _ _ _ _ _ _) hp0 (by rw [h1, Nat.cast_zero])
  set lh := ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p) with hlh
  set la := ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) 1 with hla
  have hd2 : ggDepANDot p la lh = 2 % p :=
    twNDot_eq (l05nND_AaParam_length ..) (l05nND_HaParam_length ..) (twMod_lt 2)
      (by rw [hA, hH, hα', twApply_of_mul hde, hdot2, twCast_two])
  have hmem : (lh, la) ∈ dakCells p N b.val c0.val mi ni :=
    mem_dakCells (twMod_lt s) (twMod_lt t) (twMod_lt u) h0 hd2
  obtain ⟨i, hi⟩ := kAll2_mem _ _ idx hchk _ hmem
  try dsimp only at hi
  have hval : GGTWDValid p N (lh, la) :=
    ⟨l05nND_HaParam_length .., l05nND_AaParam_length .., hd2⟩
  have htv := kTest_sound (by omega) hN hF (news := [(lh, la)])
    (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact hval) _ hi
  refine tv_back_gens hed hde hfr Set.subset_union_left ?_ htv
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  change d * ggDepARefl (ggDepANToZ p N lh) (ggDepANToZ p N la) * e ∈ _
  rw [hH, hA, twRefl_back hde ha αa α' hα']
  exact Set.mem_union_right _ (Set.mem_singleton _)

end CFSG.StandardType.DAK

end

module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Model
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309 Subgroup

@[expose] def wrKappa : Wr →* Multiplicative (ZMod 5) where
  toFun w := Multiplicative.ofAdd w.c
  map_one' := rfl
  map_mul' x y := rfl

@[expose] def wrXi : Wr →* Multiplicative (ZMod 5) where
  toFun w := Multiplicative.ofAdd (∑ i, w.a i)
  map_one' := by simp
  map_mul' x y := by
    have h : ∑ i, y.a (i - x.c) = ∑ i, y.a i := Equiv.sum_comp (Equiv.subRight x.c) y.a
    simp only [Wr.mul_a, Finset.sum_add_distrib]
    rw [h]
    rfl

theorem wr_pow_c (w : Wr) (n : ℕ) : (w ^ n).c = n • w.c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, Wr.mul_c, ih, succ_nsmul]

theorem wr_pow_a (w : Wr) (n : ℕ) (i : ZMod 5) :
    (w ^ n).a i = ∑ j ∈ Finset.range n, w.a (i - j • w.c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Wr.mul_a, ih, wr_pow_c, Finset.sum_range_succ]

theorem sum_range_five (a : ZMod 5 → ZMod 5) (c i : ZMod 5) (hc : c ≠ 0) :
    ∑ j ∈ Finset.range 5, a (i - j • c) = ∑ k, a k := by
  have hinj : ∀ c i : ZMod 5, c ≠ 0 → Function.Injective (fun j : ZMod 5 => i - j * c) := by
    decide +kernel
  have hbij : Function.Bijective (fun j : ZMod 5 => i - j * c) :=
    Finite.injective_iff_bijective.mp (hinj c i hc)
  rw [Finset.sum_range]
  have he : Function.Bijective (fun j : Fin 5 => ((j : ℕ) : ZMod 5)) := by
    have : (fun j : Fin 5 => ((j : ℕ) : ZMod 5)) = id := by
      funext j
      exact ZMod.natCast_zmod_val (n := 5) j
    rw [this]
    exact Function.bijective_id
  refine (Fintype.sum_bijective (fun j : Fin 5 => i - ((j : ℕ) : ZMod 5) * c) (hbij.comp he) _ a ?_)
  intro j
  simp [nsmul_eq_mul]

theorem wr_pow_five_of_ne {w : Wr} (hc : w.c ≠ 0) : w ^ 5 = ⟨fun _ => ∑ i, w.a i, 0⟩ := by
  ext i
  · rw [wr_pow_a, sum_range_five w.a w.c i hc]
  · rw [wr_pow_c]
    show (5 : ℕ) • w.c = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem wr_pow_five_of_eq {w : Wr} (hc : w.c = 0) : w ^ 5 = 1 := by
  ext i
  · rw [wr_pow_a, hc]
    simp only [smul_zero, sub_zero, Finset.sum_const, Finset.card_range]
    show (5 : ℕ) • w.a i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · rw [wr_pow_c, hc]
    simp

theorem wr_pow_five_eq_one_iff {w : Wr} (hc : w.c ≠ 0) : w ^ 5 = 1 ↔ ∑ i, w.a i = 0 := by
  rw [wr_pow_five_of_ne hc]
  constructor
  · intro h
    have := congrFun (congrArg Wr.a h) 0
    simpa using this
  · intro h
    ext i
    · simp [h]
    · rfl

theorem card_wrKappa_ker : Nat.card wrKappa.ker = 5 ^ 5 := by
  have e : wrKappa.ker ≃ (ZMod 5 → ZMod 5) :=
    { toFun := fun w => (w : Wr).a
      invFun := fun a => ⟨⟨a, 0⟩, rfl⟩
      left_inv := fun w => by
        refine Subtype.ext (Wr.ext rfl ?_)
        have := w.2
        rw [MonoidHom.mem_ker] at this
        exact (congrArg Multiplicative.toAdd this).symm
      right_inv := fun a => rfl }
  rw [Nat.card_congr e]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem card_wrXi_ker : Nat.card wrXi.ker = 5 ^ 5 := by
  have h := Subgroup.card_ker_mul_card_range wrXi
  have hsurj : Function.Surjective wrXi := fun t => by
    refine ⟨⟨fun i => if i = 0 then Multiplicative.toAdd t else 0, 0⟩, ?_⟩
    change Multiplicative.ofAdd (∑ i : ZMod 5, if i = 0 then Multiplicative.toAdd t else 0) = t
    simp
  have hr : wrXi.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  rw [hr, Subgroup.card_top, card_Wr] at h
  have h5 : Nat.card (Multiplicative (ZMod 5)) = 5 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [h5] at h
  omega

theorem wr_comm_of_c_zero {w w' : Wr} (hw : w.c = 0) (hw' : w'.c = 0) : w * w' = w' * w := by
  ext i
  · simp [hw, hw', add_comm]
  · simp [hw, hw']

theorem wr_pure (S : Subgroup Wr) (hScard : Nat.card S = 5 ^ 5) (hSexp : ∀ w ∈ S, w ^ 5 = 1)
    (hSnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) {x : Wr} (hxS : x ∉ S) (hx5 : x ^ 5 = 1)
    (hxc : x.c ≠ 0) : False := by
  have hxξ : ∑ i, x.a i = 0 := (wr_pow_five_eq_one_iff hxc).mp hx5
  obtain ⟨s, hsS, hsξ⟩ : ∃ s ∈ S, ∑ i, s.a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : S ≤ wrXi.ker := fun w hw => by
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (∑ i, w.a i) = 1
      rw [hcon w hw]
      rfl
    have hS : S = wrXi.ker :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hScard, card_wrXi_ker])
    apply hxS
    rw [hS, MonoidHom.mem_ker]
    change Multiplicative.ofAdd (∑ i, x.a i) = 1
    rw [hxξ]
    rfl
  have hsc : s.c = 0 := by
    by_contra hsc
    exact hsξ ((wr_pow_five_eq_one_iff hsc).mp (hSexp s hsS))
  obtain ⟨t, htS, htc⟩ : ∃ t ∈ S, t.c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : S ≤ wrKappa.ker := fun w hw => by
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd w.c = 1
      rw [hcon w hw]
      rfl
    have hS : S = wrKappa.ker :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hScard, card_wrKappa_ker])
    obtain ⟨a, ha, b, hb, hab⟩ := hSnab
    rw [hS] at ha hb
    exact hab (wr_comm_of_c_zero (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp ha))
      (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hb)))
  have htξ : ∑ i, t.a i = 0 := (wr_pow_five_eq_one_iff htc).mp (hSexp t htS)
  have huS : s * t ∈ S := S.mul_mem hsS htS
  have huc : (s * t).c ≠ 0 := by
    rw [Wr.mul_c, hsc, zero_add]
    exact htc
  have huξ : ∑ i, (s * t).a i = ∑ i, s.a i + ∑ i, t.a i := by
    have h := congrArg Multiplicative.toAdd (wrXi.map_mul s t)
    exact h
  exact hsξ (by
    have := (wr_pow_five_eq_one_iff huc).mp (hSexp _ huS)
    rw [huξ, htξ, add_zero] at this
    exact this)

theorem wr_exclusion {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} (ψ : ↥P →* Wr)
    (hψ : Function.Injective ψ) (hcard : Nat.card P = 5 ^ 6) {S : Subgroup Y} (hSP : S ≤ P)
    (hScard : Nat.card S = 5 ^ 5) (hSexp : ∀ s ∈ S, s ^ 5 = 1)
    (hSnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) {x : Y} (hxP : x ∈ P) (hxS : x ∉ S)
    (hx5 : x ^ 5 = 1) : 5 ≤ CFSG.Open.pRank 5 (centralizer ({x} : Set Y)) := by
  classical
  have hbij : Function.Bijective ψ :=
    hψ.bijective_of_nat_card_le (by rw [card_Wr, hcard])
  have hsurj : Function.Surjective ψ := hbij.2
  set x' : ↥P := ⟨x, hxP⟩ with hx'
  by_cases hc : (ψ x').c = 0
  ·
    set E : Subgroup Y := ((wrKappa.ker).comap ψ).map P.subtype with hE
    have hEmem : ∀ y : Y, y ∈ E ↔ ∃ hy : y ∈ P, (ψ ⟨y, hy⟩).c = 0 := by
      intro y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u.2, congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hu)⟩
      · rintro ⟨hy, hyc⟩
        refine ⟨⟨y, hy⟩, MonoidHom.mem_ker.mpr (congrArg Multiplicative.ofAdd hyc), rfl⟩
    have hcomm : ∀ a b : Y, a ∈ E → b ∈ E → a * b = b * a := by
      intro a b ha hb
      obtain ⟨ha1, hac⟩ := (hEmem a).mp ha
      obtain ⟨hb1, hbc⟩ := (hEmem b).mp hb
      have := wr_comm_of_c_zero hac hbc
      have h2 : ψ (⟨a, ha1⟩ * ⟨b, hb1⟩) = ψ (⟨b, hb1⟩ * ⟨a, ha1⟩) := by
        rw [map_mul, map_mul]
        exact this
      exact congrArg Subtype.val (hψ h2)
    have hEab : CFSG.Open.IsElemAbelian 5 E := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a b a.2 b.2)⟩⟩, fun y hy => ?_⟩
      obtain ⟨hy1, hyc⟩ := (hEmem y).mp hy
      have h1 : ψ (⟨y, hy1⟩ ^ 5) = ψ 1 := by
        rw [map_pow, map_one]
        exact wr_pow_five_of_eq hyc
      have h2 := hψ h1
      exact congrArg Subtype.val h2
    have hEcard : Nat.card E = 5 ^ 5 := by
      have h1 : Nat.card E = Nat.card ((wrKappa.ker).comap ψ) :=
        Subgroup.card_map_of_injective P.subtype_injective
      have h2 : Nat.card ((wrKappa.ker).comap ψ) = Nat.card wrKappa.ker := by
        have := Subgroup.card_map_of_injective hψ (K := (wrKappa.ker).comap ψ)
        rw [Subgroup.map_comap_eq_self_of_surjective hsurj] at this
        exact this.symm
      rw [h1, h2, card_wrKappa_ker]
    have hEx : E ≤ centralizer ({x} : Set Y) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm x y ((hEmem x).mpr ⟨hxP, hc⟩) hy |>.symm
    exact CFSG.SectionRank.le_pRank (by norm_num) hEx hEab hEcard
  · exfalso
    refine wr_pure (x := ψ x') ((S.subgroupOf P).map ψ) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective hψ,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv, hScard]
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow]
      have : u ^ 5 = 1 := Subtype.ext (hSexp u (Subgroup.mem_subgroupOf.mp hu))
      rw [this, map_one]
    · obtain ⟨a, ha, b, hb, hab⟩ := hSnab
      refine ⟨ψ ⟨a, hSP ha⟩, ⟨⟨a, hSP ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩,
        ψ ⟨b, hSP hb⟩, ⟨⟨b, hSP hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩, fun h => hab ?_⟩
      rw [← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (hψ h)
    · rintro ⟨u, hu, hux⟩
      exact hxS (by
        have := hψ hux
        rw [this] at hu
        exact Subgroup.mem_subgroupOf.mp hu)
    · rw [← map_pow]
      have : x' ^ 5 = 1 := Subtype.ext hx5
      rw [this, map_one]
    · exact hc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

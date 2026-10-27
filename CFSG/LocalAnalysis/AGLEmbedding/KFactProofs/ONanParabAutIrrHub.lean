module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

section Derived

theorem exists_derivedSeries_perfect (H : Type*) [Group H] [Finite H] :
    ∃ m : ℕ, ⁅derivedSeries H m, derivedSeries H m⁆ = derivedSeries H m := by
  obtain ⟨x, y, hxy, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => derivedSeries H n)
  wlog hlt : x < y generalizing x y
  · exact this y x hxy.symm h.symm (lt_of_le_of_ne (not_lt.1 hlt) hxy.symm)
  refine ⟨x, ?_⟩
  have h1 : derivedSeries H y ≤ derivedSeries H (x + 1) := derivedSeries_antitone H hlt
  have h2 : derivedSeries H (x + 1) ≤ derivedSeries H x := derivedSeries_antitone H (Nat.le_succ x)
  have h3 : derivedSeries H (x + 1) = derivedSeries H x := le_antisymm h2 (h ▸ h1)
  rw [← derivedSeries_succ]
  exact h3

theorem eq_bot_of_perfect {Q : Type*} [Group Q] {m : ℕ} (hm : derivedSeries Q m = ⊥)
    {V : Subgroup Q} (hV : ⁅V, V⁆ = V) : V = ⊥ := by
  have : ∀ n, V ≤ derivedSeries Q n := by
    intro n
    induction n with
    | zero => simp [derivedSeries_zero]
    | succ n ih =>
      rw [derivedSeries_succ]
      calc V = ⁅V, V⁆ := hV.symm
        _ ≤ ⁅derivedSeries Q n, derivedSeries Q n⁆ := Subgroup.commutator_mono ih ih
  rw [← le_bot_iff, ← hm]
  exact this m

theorem perfect_iff_map_subtype {H : Type*} [Group H] (Jh : Subgroup H) (A : Subgroup Jh) :
    ⁅A, A⁆ = A ↔ ⁅A.map Jh.subtype, A.map Jh.subtype⁆ = A.map Jh.subtype := by
  rw [← Subgroup.map_commutator, (Subgroup.map_injective Jh.subtype_injective).eq_iff]

theorem perfect_subgroupOf_iff {H : Type*} [Group H] {Jh A : Subgroup H} (hA : A ≤ Jh) :
    ⁅A.subgroupOf Jh, A.subgroupOf Jh⁆ = A.subgroupOf Jh ↔ ⁅A, A⁆ = A := by
  rw [perfect_iff_map_subtype, Subgroup.map_subgroupOf_eq_of_le hA]

theorem commutes_subgroupOf {H : Type*} [Group H] {Jh A B : Subgroup H} (h : Commutes A B) :
    Commutes (A.subgroupOf Jh) (B.subgroupOf Jh) := by
  intro a ha b hb
  apply Subtype.ext
  exact h a ha b hb

theorem card_subgroupOf {H : Type*} [Group H] {Jh A : Subgroup H} (hA : A ≤ Jh) :
    Nat.card (A.subgroupOf Jh) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem map_subtype_sup_subgroupOf {H : Type*} [Group H] {Jh A B : Subgroup H} (hA : A ≤ Jh)
    (hB : B ≤ Jh) : (A.subgroupOf Jh ⊔ B.subgroupOf Jh).map Jh.subtype = A ⊔ B := by
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hB]

end Derived

section Images

theorem card_map_dvd_two {H Q : Type*} [Group H] [Finite H] [Group Q] {φ : H →* Q}
    {V S : Subgroup H} (hVS : V ≤ S) (hV : V ≤ φ.ker) (h : Nat.card S ∣ 2 * Nat.card V) :
    Nat.card (S.map φ) ∣ 2 := by
  have h1 := Subgroup.card_ker_mul_card_range (φ.comp S.subtype)
  have hr : (φ.comp S.subtype).range = S.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr] at h1
  have hV1 : V.subgroupOf S ≤ (φ.comp S.subtype).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.1 (hV (Subgroup.mem_subgroupOf.1 hx))
  have h2 : Nat.card (V.subgroupOf S) ∣ Nat.card (φ.comp S.subtype).ker :=
    Subgroup.card_dvd_of_le hV1
  rw [card_subgroupOf hVS] at h2
  have hpos : 0 < Nat.card (φ.comp S.subtype).ker := Nat.card_pos
  have h4 : Nat.card (φ.comp S.subtype).ker * Nat.card (S.map φ) ∣
      Nat.card (φ.comp S.subtype).ker * 2 := by
    rw [h1, mul_comm]
    exact h.trans (Nat.mul_dvd_mul_left 2 h2)
  exact Nat.dvd_of_mul_dvd_mul_left hpos h4

end Images

section LeviIdx

structure LeviIdx {G : Type*} [Group G] {ι : Type*} (L : ι → Subgroup G) (p : ℕ)
    (adj exc : ι → ι → Prop) : Prop where
  adj_symm : ∀ i j, adj i j → adj j i
  comm : ∀ i j, i ≠ j → ¬ adj i j → Commutes (L i) (L j)
  node : ∀ i, ⁅L i, L i⁆ = L i ∨ ¬ p ∣ Nat.card (L i)
  pair : ∀ i j, i ≠ j → adj i j → ⁅L i, L i⁆ ≠ L i → ⁅L j, L j⁆ ≠ L j →
    ⁅L i ⊔ L j, L i ⊔ L j⁆ = L i ⊔ L j ∨ exc i j
  exc_symm : ∀ i j, exc i j → exc j i
  exc_unique : ∀ i j k, exc i j → exc i k → j = k
  exc_idx : ∀ i j, exc i j → ∃ V : Subgroup G, V ≤ L i ⊔ L j ∧ ⁅V, V⁆ = V ∧
    Nat.card ↥(L i ⊔ L j) ∣ 2 * Nat.card V

variable {H Q : Type*} [Group H] [Finite H] [Group Q] {ι : Type*} {L : ι → Subgroup H} {p : ℕ}
  {adj exc : ι → ι → Prop}

theorem LeviIdx.leviData_map (hp5 : 5 ≤ p) (hL : LeviIdx L p adj exc) {Jh : Subgroup H}
    (I : Finset ι) (hLJ : ∀ i ∈ I, L i ≤ Jh) (φ : ↥Jh →* Q)
    (hQ : ∀ V : Subgroup Q, ⁅V, V⁆ = V → V = ⊥) :
    LeviData (fun i : I => ((L i).subgroupOf Jh).map φ) p (fun i j => adj i j)
      (fun i j => exc i j) := by
  have hperf : ∀ i : I, ⁅L i, L i⁆ = L i →
      ⁅((L i).subgroupOf Jh).map φ, ((L i).subgroupOf Jh).map φ⁆ =
        ((L i).subgroupOf Jh).map φ := fun i h =>
    map_commutator_self_eq φ ((perfect_subgroupOf_iff (hLJ i i.2)).2 h)
  have hnonperf : ∀ i : I,
      ⁅((L i).subgroupOf Jh).map φ, ((L i).subgroupOf Jh).map φ⁆ ≠
        ((L i).subgroupOf Jh).map φ → ⁅L i, L i⁆ ≠ L i := fun i h h' => h (hperf i h')
  refine
  { adj_symm := fun i j h => hL.adj_symm i j h
    comm := fun i j hij hadj => ?_
    node := fun i => ?_
    pair := fun i j hij hadj hi hj => ?_
    exc_symm := fun i j h => hL.exc_symm i j h
    exc_unique := fun i j k hij hik => Subtype.ext (hL.exc_unique i j k hij hik)
    exc_perfect := fun i j h => ?_ }
  · exact (commutes_subgroupOf (hL.comm i j (fun h => hij (Subtype.ext h)) hadj)).map φ
  · rcases hL.node i with h | h
    · exact Or.inl (hperf i h)
    · refine Or.inr fun hd => h ?_
      have h1 := hd.trans (Subgroup.card_map_dvd ((L i).subgroupOf Jh) φ)
      rwa [card_subgroupOf (hLJ i i.2)] at h1
  · rcases hL.pair i j (fun h => hij (Subtype.ext h)) hadj (hnonperf i hi) (hnonperf j hj) with
      h | h
    · left
      have hij' : (L i ⊔ L j) ≤ Jh := sup_le (hLJ i i.2) (hLJ j j.2)
      rw [← Subgroup.map_sup]
      refine map_commutator_self_eq φ ?_
      rw [perfect_iff_map_subtype, map_subtype_sup_subgroupOf (hLJ i i.2) (hLJ j j.2)]
      exact h
    · exact Or.inr h
  · obtain ⟨V, hVS, hV, hVc⟩ := hL.exc_idx i j h
    refine ⟨⊥, bot_le, by simp, fun hd => ?_⟩
    have hSJ : L i ⊔ L j ≤ Jh := sup_le (hLJ i i.2) (hLJ j j.2)
    have hVJ : V ≤ Jh := hVS.trans hSJ
    set S : Subgroup Jh := (L i).subgroupOf Jh ⊔ (L j).subgroupOf Jh with hS
    have hSmap : S.map Jh.subtype = L i ⊔ L j :=
      map_subtype_sup_subgroupOf (hLJ i i.2) (hLJ j j.2)
    set V₁ : Subgroup Jh := V.subgroupOf Jh with hV₁
    have hV₁map : V₁.map Jh.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVJ
    have hV₁S : V₁ ≤ S := by
      rw [← Subgroup.map_le_map_iff_of_injective Jh.subtype_injective, hV₁map, hSmap]
      exact hVS
    have hV₁perf : ⁅V₁, V₁⁆ = V₁ := (perfect_subgroupOf_iff hVJ).2 hV
    have hker : V₁ ≤ φ.ker := by
      have := hQ _ (map_commutator_self_eq φ hV₁perf)
      rw [← Subgroup.map_eq_bot_iff]
      exact this
    have hcard : Nat.card S ∣ 2 * Nat.card V₁ := by
      have e1 : Nat.card S = Nat.card (S.map Jh.subtype) :=
        (Subgroup.card_map_of_injective Jh.subtype_injective).symm
      have e2 : Nat.card V₁ = Nat.card V := card_subgroupOf hVJ
      rw [e1, e2, hSmap]
      exact hVc
    have h2 := card_map_dvd_two hV₁S hker hcard
    have e3 : ((L i).subgroupOf Jh).map φ ⊔ ((L j).subgroupOf Jh).map φ = S.map φ := by
      rw [hS, Subgroup.map_sup]
    have hd' : p ∣ Nat.card ↥(((L i).subgroupOf Jh).map φ ⊔ ((L j).subgroupOf Jh).map φ) := hd
    rw [e3] at hd'
    have := Nat.le_of_dvd (by norm_num) (hd'.trans h2)
    exfalso
    omega

end LeviIdx

section Main

theorem mem_perfectJoin_of_leviIdx {K G : Type*} [Group K] [Finite K] [Group G] [Finite G]
    (π : K →* G) {J : Subgroup G} {ι : Type*} [DecidableEq ι] {L : ι → Subgroup K} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {adj exc : ι → ι → Prop} (hL : LeviIdx L p adj exc)
    (I : Finset ι) (hLJ : ∀ i ∈ I, L i ≤ J.comap π) {B : Subgroup K} (hBJ : B ≤ J.comap π)
    (hpB : ¬ p ∣ Nat.card (B.map π))
    (hJ : ∀ x ∈ J, ∃ a ∈ ⨆ i ∈ I, L i, ∃ b ∈ B, x = π (a * b))
    {g : G} (hgJ : g ∈ J) {a : ℕ} (hga : g ^ p ^ a = 1) : g ∈ perfectJoin J := by
  classical
  set Jh : Subgroup K := J.comap π with hJh
  let φ₀ : ↥Jh →* ↥J := (π.comp Jh.subtype).codRestrict J (fun x => x.2)
  have hφ₀ : ∀ x : ↥Jh, ((φ₀ x : ↥J) : G) = π x := fun x => rfl
  obtain ⟨m, hm⟩ := exists_derivedSeries_perfect ↥J
  set Wt : Subgroup ↥J := derivedSeries ↥J m with hWt
  have hWn : Wt.Normal := derivedSeries_normal ↥J m
  let qq : ↥J →* ↥J ⧸ Wt := QuotientGroup.mk' Wt
  let φ : ↥Jh →* ↥J ⧸ Wt := qq.comp φ₀
  have hQm : derivedSeries (↥J ⧸ Wt) m = ⊥ := by
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective Wt) m, ← hWt,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hQ : ∀ V : Subgroup (↥J ⧸ Wt), ⁅V, V⁆ = V → V = ⊥ := fun V hV => eq_bot_of_perfect hQm hV
  have hLD := hL.leviData_map hp5 I hLJ φ hQ
  set Λ' : Subgroup (↥J ⧸ Wt) :=
    ⨆ i ∈ (Finset.univ : Finset I), ((L i).subgroupOf Jh).map φ with hΛ'
  have hnd : ¬ p ∣ Nat.card Λ' := by
    intro hd
    obtain ⟨V, -, hV, hpV⟩ := exists_perfect_dvd_of_leviData hp hp5 hLD Finset.univ hd
    rw [hQ V hV, Subgroup.card_bot] at hpV
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpV)
  set B'' : Subgroup (↥J ⧸ Wt) := ((B.map π).subgroupOf J).map qq with hB''
  have hBπ : B.map π ≤ J := by
    rintro _ ⟨b, hb, rfl⟩
    exact hBJ hb
  have hpB'' : ¬ p ∣ Nat.card B'' := by
    intro hd
    apply hpB
    have h1 := hd.trans (Subgroup.card_map_dvd ((B.map π).subgroupOf J) qq)
    rwa [card_subgroupOf hBπ] at h1
  have hΛmem : ∀ x ∈ ⨆ i ∈ I, L i, ∃ h : x ∈ Jh, φ ⟨x, h⟩ ∈ Λ' := by
    intro x hx
    refine iSup₂_induction (C := fun x => ∃ h : x ∈ Jh, φ ⟨x, h⟩ ∈ Λ') hx ?_ ?_ ?_
    · intro i hi y hy
      refine ⟨hLJ i hi hy, ?_⟩
      have : φ ⟨y, hLJ i hi hy⟩ ∈ ((L i).subgroupOf Jh).map φ :=
        ⟨⟨y, hLJ i hi hy⟩, hy, rfl⟩
      exact (le_iSup₂_of_le (⟨i, hi⟩ : I) (Finset.mem_univ _) le_rfl : ((L i).subgroupOf Jh).map φ ≤
        Λ') this
    · refine ⟨one_mem _, ?_⟩
      rw [show (⟨1, one_mem _⟩ : ↥Jh) = 1 from rfl, map_one]
      exact Λ'.one_mem
    · rintro y z ⟨hy, hyΛ⟩ ⟨hz, hzΛ⟩
      refine ⟨mul_mem hy hz, ?_⟩
      have := mul_mem hyΛ hzΛ
      simpa [← map_mul] using this
  have hcover : ∀ z : ↥J ⧸ Wt, ∃ x ∈ Λ', ∃ b ∈ B'', z = x * b := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨x, hxΛ, b, hbB, hy⟩ := hJ y.1 y.2
    obtain ⟨hxJ, hxφ⟩ := hΛmem x hxΛ
    have hbJ : b ∈ Jh := hBJ hbB
    refine ⟨φ ⟨x, hxJ⟩, hxφ, qq ⟨π b, hbJ⟩, ⟨⟨π b, hbJ⟩, ⟨b, hbB, rfl⟩, rfl⟩, ?_⟩
    have hyeq : y = φ₀ ⟨x, hxJ⟩ * ⟨π b, hbJ⟩ := Subtype.ext (by
      rw [Subgroup.coe_mul, hφ₀]
      show (y : G) = π x * π b
      rw [hy, map_mul])
    show qq y = qq (φ₀ ⟨x, hxJ⟩) * qq ⟨π b, hbJ⟩
    rw [← map_mul, ← hyeq]
  have hQcard : Nat.card (↥J ⧸ Wt) ∣ Nat.card Λ' * Nat.card B'' := by
    have := card_dvd_mul_of_forall_mem_mul (J := (⊤ : Subgroup (↥J ⧸ Wt))) (A := Λ') (B := B'')
      le_top le_top (fun x _ => by simpa using hcover x)
    simpa [Subgroup.card_top] using this
  have hpQ : ¬ p ∣ Nat.card (↥J ⧸ Wt) := by
    intro hd
    rcases hp.dvd_mul.1 (hd.trans hQcard) with h | h
    · exact hnd h
    · exact hpB'' h
  set y₀ : ↥J := ⟨g, hgJ⟩ with hy₀
  have hz : (qq y₀) ^ p ^ a = 1 := by
    rw [← map_pow]
    have : y₀ ^ p ^ a = 1 := Subtype.ext (by simpa [hy₀] using hga)
    rw [this, map_one]
  have hord1 : orderOf (qq y₀) ∣ p ^ a := orderOf_dvd_of_pow_eq_one hz
  have hord2 : orderOf (qq y₀) ∣ Nat.card (↥J ⧸ Wt) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ a) (Nat.card (↥J ⧸ Wt)) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpQ)
  have hord : orderOf (qq y₀) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord1 hcop) hord2
  have hyW : y₀ ∈ Wt := (QuotientGroup.eq_one_iff y₀).1 (orderOf_eq_one_iff.1 hord)
  have hWperf : ⁅Wt.map J.subtype, Wt.map J.subtype⁆ = Wt.map J.subtype :=
    (perfect_iff_map_subtype J Wt).1 hm
  have hWJ : Wt.map J.subtype ≤ J := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  exact le_perfectJoin hWJ hWperf ⟨y₀, hyW, rfl⟩

end Main

end CFSG.AGLEmbedding.ParabAutIrr

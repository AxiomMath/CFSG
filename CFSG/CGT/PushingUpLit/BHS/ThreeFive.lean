module

public import CFSG.CGT.PushingUpLit.BHS.ThreeFiveG

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

variable {V : Type} [CommGroup V]

theorem isSylowOf_subgroupOf_top {Γ : Type*} [Group Γ] {P T : Subgroup Γ} (h : IsSylowOf 2 T P) :
    IsSylowOf 2 (T.subgroupOf P) (⊤ : Subgroup ↥P) := by
  refine ⟨le_top, h.2.1.comap_subtype (K := P), ?_⟩
  have : (T.subgroupOf P).relIndex ⊤ = T.relIndex P := by
    rw [Subgroup.relIndex_top_right]
    rfl
  rw [this]
  exact h.2.2

theorem MinPar.subgroupOf_top {Γ : Type*} [Group Γ] {P T M : Subgroup Γ} (h : MinPar P T M) :
    MinPar (⊤ : Subgroup ↥P) (T.subgroupOf P) (M.subgroupOf P) where
  syl := isSylowOf_subgroupOf_top h.syl
  not_normal := fun hn => h.not_normal
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.T_le).1
      ⟨fun x hx g => (Subgroup.mem_normalizer_iff.1 (hn (Subgroup.mem_top g)) x).1 hx⟩)
  le_M := Subgroup.subgroupOf_mono P h.le_M
  lt_P := lt_top_iff_ne_top.2 fun e => h.lt_P.not_ge (Subgroup.subgroupOf_eq_top.1 e)
  max := fun X hTX hX => by
    have hX' : X.map P.subtype < P := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le X) fun e => hX.ne ?_
      rw [eq_top_iff]
      intro y _
      have hy : (y : Γ) ∈ X.map P.subtype := by rw [e]; exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      have : x = y := Subtype.ext hxy
      exact this ▸ hx
    have hTX' : T ≤ X.map P.subtype := fun t ht =>
      ⟨⟨t, h.T_le ht⟩, hTX (Subgroup.mem_subgroupOf.2 ht), rfl⟩
    have := h.max _ hTX' hX'
    exact fun x hx => this ⟨x, hx, rfl⟩

theorem map_subtype_conj {Γ : Type*} [Group Γ] (P : Subgroup Γ) (x : ↥P) (Y : Subgroup ↥P) :
    (Y.map (MulAut.conj x).toMonoidHom).map P.subtype =
      conjSub (x : Γ) (Y.map P.subtype) := by
  rw [conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem ThreeFiveHyp.of_ambient {P T M A : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hmin : MinPar P T M) (hAT : A ≤ T) (hel : IsElemAbelian2 A) (hcard : Nat.card V ≤ wt A)
    (hlt : ∀ B : Subgroup (MulAut V), B ≤ A → B ≠ ⊥ → B ≠ A → wt B < wt A)
    (hnt : ∃ g ∈ P, ∃ z ∈ fixV T, g z ≠ z)
    (hgen : ∀ x ∈ P, x ∉ M → A ⊔ conjSub x A = P) :
    ThreeFiveHyp P.subtype (T.subgroupOf P) (M.subgroupOf P) (A.subgroupOf P) := by
  have hAP : A ≤ P := hAT.trans hmin.T_le
  have hmapA : (A.subgroupOf P).map P.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAP
  have hmapT : (T.subgroupOf P).map P.subtype = T := Subgroup.map_subgroupOf_eq_of_le hmin.T_le
  refine
  { hV := hV
    faithful := fun a b h => Subtype.ext h
    minpar := hmin.subgroupOf_top
    le_T := fun x hx => hAT hx
    elemAb := by rw [hmapA]; exact hel
    card_le := by rw [hmapA]; exact hcard
    lt_wt := by
      rw [hmapA]
      exact hlt
    nontriv := ?_
    gen := ?_ }
  · obtain ⟨g, hgP, z, hz, hne⟩ := hnt
    exact ⟨⟨g, hgP⟩, z, by rw [hmapT]; exact hz, hne⟩
  · intro x hx
    apply Subgroup.map_injective (Subgroup.subtype_injective P)
    rw [Subgroup.map_sup, map_subtype_conj, hmapA, Subgroup.map_top, Subgroup.range_subtype]
    exact hgen x x.2 fun hxM => hx hxM

theorem three_five [Finite V] {P T M A : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M) (hAT : A ≤ T) (hel : IsElemAbelian2 A)
    (hcard : Nat.card V ≤ wt A)
    (hlt : ∀ B : Subgroup (MulAut V), B ≤ A → B ≠ ⊥ → B ≠ A → wt B < wt A)
    (hnt : ∃ g ∈ P, ∃ z ∈ fixV T, g z ≠ z) (hgen : ∀ x ∈ P, x ∉ M → A ⊔ conjSub x A = P) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card A = 2 ^ n ∧ Nat.card V = wt A ∧
      fixV A = commV A ⊔ fixV P ∧ (∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A) ∧
      IsSLNatSection P ⊤ (fixV P) n := by
  have hH := ThreeFiveHyp.of_ambient hV hmin hAT hel hcard hlt hnt hgen
  obtain ⟨n, hn1, hAn, -, hVc, hfix, hzp, θ, β, hsurj, hker, hequiv⟩ := hH.three_five_abs
  have hAP : A ≤ P := hAT.trans hmin.T_le
  have hmapA : (A.subgroupOf P).map P.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAP
  have hrange : P.subtype.range = P := Subgroup.range_subtype P
  have hAcard : Nat.card (A.subgroupOf P) = Nat.card A := by
    have := Subgroup.card_map_of_injective (Subgroup.subtype_injective P) (K := A.subgroupOf P)
    rw [hmapA] at this
    exact this.symm
  rw [hmapA] at hVc
  rw [hmapA, hrange] at hfix
  refine ⟨n, hn1, hAcard ▸ hAn, ?_, hfix, ?_, ?_⟩
  · rw [hVc, hAcard]
    rfl
  · intro a ha ha1
    have := hzp ⟨a, hAP ha⟩ (Subgroup.mem_subgroupOf.2 ha)
      (fun h => ha1 (congrArg Subtype.val h))
    rw [hmapA] at this
    exact this
  · refine ⟨fun x _ p _ => trivial, θ, β.comp (⊤ : Subgroup V).subtype, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨v, hv⟩ := hsurj y
      exact ⟨⟨v, Subgroup.mem_top v⟩, hv⟩
    · ext p
      show β p.1 = 1 ↔ p ∈ (fixV P).subgroupOf ⊤
      rw [← MonoidHom.mem_ker, hker, hrange]
      rfl
    · intro x p hp
      exact hequiv x p.1

end CFSG.CGT.PushingUpLit.BHS

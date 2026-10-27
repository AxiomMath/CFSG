module

public import CFSG.GH74.GLS.Balance.Bender.AuxRes
public import CFSG.GH74.GLS.Balance.Bender.AuxSylow
public import CFSG.GH74.GLS.Balance.Bender.OpStarP

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem mem_normalizer_of_conj {N : Subgroup G} {g : G} (h : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h' : ∀ x ∈ N, g⁻¹ * x * g⁻¹⁻¹ ∈ N) : g ∈ normalizer (N : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  exact ⟨fun hx => h x hx, fun hx => by simpa [mul_assoc] using h' _ hx⟩

omit [Finite G] [Fact p.Prime] in
theorem mem_normalizer_inf {X Z : Subgroup G} {g : G} (hX : g ∈ normalizer (X : Set G))
    (hZ : g ∈ normalizer (Z : Set G)) : g ∈ normalizer ((X ⊓ Z : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hX hZ ⊢
  intro x
  constructor
  · intro hx; exact ⟨(hX x).1 hx.1, (hZ x).1 hx.2⟩
  · intro hx; exact ⟨(hX x).2 hx.1, (hZ x).2 hx.2⟩

omit [Finite G] [Fact p.Prime] in
theorem mem_normalizer_centralizer {P : Subgroup G} {g : G} (hg : g ∈ normalizer (P : Set G)) :
    g ∈ normalizer ((centralizer (P : Set G) : Subgroup G) : Set G) := by
  have hg' : g⁻¹ ∈ normalizer (P : Set G) := (normalizer (P : Set G)).inv_mem hg
  have key : ∀ g : G, g ∈ normalizer (P : Set G) → ∀ c ∈ centralizer (P : Set G),
      g * c * g⁻¹ ∈ centralizer (P : Set G) := by
    intro g hg c hc
    rw [mem_centralizer_iff]
    intro h hh
    have hh' : g⁻¹ * h * g⁻¹⁻¹ ∈ P := by
      have hg'' : g⁻¹ ∈ normalizer (P : Set G) := (normalizer (P : Set G)).inv_mem hg
      exact (mem_normalizer_iff.mp hg'' h).mp hh
    have hcomm := mem_centralizer_iff.mp hc _ hh'
    simp only [inv_inv] at hh' hcomm
    calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm]
      _ = g * c * g⁻¹ * h := by group
  exact mem_normalizer_of_conj (fun x hx => key g hg x hx) (fun x hx => key g⁻¹ hg' x hx)

omit [Finite G] [Fact p.Prime] in
theorem normal_subgroupOf_of_conj {N Z : Subgroup G}
    (h : ∀ g ∈ Z, ∀ x ∈ N, g * x * g⁻¹ ∈ N) : (N.subgroupOf Z).Normal :=
  ⟨fun n hn g => h g g.2 n hn⟩

omit [Finite G] [Fact p.Prime] in
theorem oResOf_normal (p : ℕ) (Y : Subgroup G) : ((oResOf p Y).subgroupOf Y).Normal :=
  normal_subgroupOf_of_conj fun _ hg _ hx =>
    oResOf_conj_mem (Subgroup.le_normalizer hg) hx

omit [Finite G] [Fact p.Prime] in
theorem oResOf_oResOf (p : ℕ) (Y : Subgroup G) : oResOf p (oResOf p Y) = oResOf p Y := by
  apply le_antisymm (oResOf_le p _)
  refine oResOf_le_of fun x hx hxo => ?_
  exact mem_oResOf (mem_oResOf hx hxo) hxo

def PropB (p : ℕ) (X : Subgroup G) : Prop :=
  ∀ P : Subgroup G, IsPGroup p ↥P → P ≤ normalizer (X : Set G) →
    OpStar p (X ⊓ centralizer (P : Set G)) ≤ OpStar p X

theorem chain_le {X : Subgroup G} (IHB : ∀ Y : Subgroup G, Nat.card Y < Nat.card X → PropB p Y) :
    ∀ m : ℕ, ∀ P P' : Subgroup G, Nat.card P' - Nat.card P = m → IsPGroup p ↥P' → P ≤ P' →
      P' ≤ normalizer (X : Set G) → ¬ X ≤ centralizer (P : Set G) →
      OpStar p (X ⊓ centralizer (P' : Set G)) ≤ OpStar p (X ⊓ centralizer (P : Set G)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro P P' hm hP' hPP' hnorm hnc
    by_cases hle : P' ≤ P
    · have : P' = P := le_antisymm hle hPP'
      subst this
      exact le_rfl
    · obtain ⟨g, hgP', hgN, hgP⟩ := exists_mem_normalizer_not_mem hP' hPP' hle
      set P₁ : Subgroup G := P ⊔ Subgroup.zpowers g with hP₁
      have hP₁P' : P₁ ≤ P' := sup_le hPP' ((Subgroup.zpowers_le).2 hgP')
      have hP₁p : IsPGroup p ↥P₁ := hP'.to_le hP₁P'
      have hPP₁ : P ≤ P₁ := le_sup_left
      have hP₁n : P₁ ≤ normalizer (P : Set G) :=
        sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hgN)
      have hgP₁ : g ∈ P₁ := (le_sup_right : Subgroup.zpowers g ≤ P₁) (Subgroup.mem_zpowers g)
      have hlt1 : P < P₁ := lt_of_le_of_ne hPP₁ fun h => hgP (h ▸ hgP₁)
      have hc1 : Nat.card P < Nat.card P₁ := Subgroup.card_lt_of_lt hlt1
      have hc2 : Nat.card P₁ ≤ Nat.card P' := Subgroup.card_le_of_le hP₁P'
      set Y : Subgroup G := X ⊓ centralizer (P : Set G) with hY
      have hYX : Y < X := lt_of_le_of_ne inf_le_left fun h => hnc (h ▸ inf_le_right)
      have hP₁Y : P₁ ≤ normalizer (Y : Set G) := fun g' hg' =>
        mem_normalizer_inf (hnorm (hP₁P' hg')) (mem_normalizer_centralizer (hP₁n hg'))
      have hstep1 := IHB Y (Subgroup.card_lt_of_lt hYX) P₁ hP₁p hP₁Y
      have heq : Y ⊓ centralizer (P₁ : Set G) = X ⊓ centralizer (P₁ : Set G) := by
        rw [hY, inf_assoc]
        congr 1
        exact inf_eq_right.2 (Subgroup.centralizer_le fun x hx => hPP₁ hx)
      rw [heq] at hstep1
      have hnc₁ : ¬ X ≤ centralizer (P₁ : Set G) := fun h =>
        hnc (h.trans (Subgroup.centralizer_le fun x hx => hPP₁ hx))
      have hstep2 := ih (Nat.card P' - Nat.card P₁) (by omega) P₁ P' rfl hP' hP₁P' hnorm hnc₁
      exact hstep2.trans hstep1

def PropA (p : ℕ) [Fact p.Prime] (X : Subgroup G) : Prop :=
  ∀ P : Subgroup G, IsPStar p ↥X → IsPGroup p ↥P → P ≤ normalizer (X : Set G) →
    X ≤ ⁅X, P⁆ ⊔ OpStar p (X ⊓ centralizer (P : Set G))

theorem propB (h56 : BenderL56 p) (h59 : BenderT59 p) {X : Subgroup G}
    (IH : ∀ Y : Subgroup G, Nat.card Y < Nat.card X → PropA p Y ∧ PropB p Y) : PropB p X := by
  by_contra hB
  simp only [PropB, not_forall] at hB
  obtain ⟨P₀, hP₀, hP₀n, hP₀bad⟩ := hB
  set 𝒞 : Set (Subgroup G) := {P | IsPGroup p ↥P ∧ P ≤ normalizer (X : Set G) ∧
    ¬ OpStar p (X ⊓ centralizer (P : Set G)) ≤ OpStar p X} with h𝒞
  obtain ⟨P, ⟨hP, hPn, hPbad⟩, hPmax⟩ :=
    Set.exists_max_image 𝒞 (fun P => Nat.card P) (Set.toFinite 𝒞) ⟨P₀, hP₀, hP₀n, hP₀bad⟩
  have hnc : ¬ X ≤ centralizer (P : Set G) := by
    intro h
    apply hPbad
    rw [inf_eq_left.2 h]
  set Y : Subgroup G := X ⊓ centralizer (P : Set G) with hY
  set L : Subgroup G := OpStar p Y with hL
  set O : Subgroup G := OpStar p X with hO
  set K : Subgroup G := OpStarP p X with hK
  have hLp : IsPStar p ↥L := isPStar_opStar h56 Y
  have hLK : ¬ L ≤ K := by
    intro hLK
    apply hPbad
    calc L = oResOf p L := hLp.oResOf_eq.symm
      _ ≤ oResOf p K := oResOf_mono hLK
      _ ≤ O := oResOf_opStarP_le p X
  have hKn : P ≤ normalizer (K : Set G) := fun g hg =>
    mem_normalizer_of_conj (fun x hx => opStarP_conj_mem (hPn hg) hx) (fun x hx =>
      opStarP_conj_mem ((normalizer (X : Set G)).inv_mem (hPn hg)) hx)
  obtain ⟨S, hS, hPS⟩ := exists_invariant_sylow hP hKn
  have hSp : IsPGroup p ↥S := hS.2.1
  have hSK : S ≤ K := hS.1
  set S₀ : Subgroup G := S ⊓ normalizer (P : Set G) with hS₀
  have hS₀p : IsPGroup p ↥S₀ := hSp.to_inf_left
  have hLX : Nat.card L < Nat.card X := by
    have hLY : L ≤ Y := opStar_le p Y
    have hYX : Y < X := lt_of_le_of_ne inf_le_left fun h => hnc (h ▸ inf_le_right)
    exact Subgroup.card_lt_of_lt (lt_of_le_of_lt hLY hYX)
  have hS₀L : S₀ ≤ normalizer (L : Set G) := by
    intro g hg
    have hgY : g ∈ normalizer (Y : Set G) :=
      mem_normalizer_inf (Subgroup.le_normalizer (opStarP_le p X (hSK hg.1)))
        (mem_normalizer_centralizer hg.2)
    exact mem_normalizer_of_conj (fun x hx => opStar_conj_mem hgY hx) (fun x hx =>
      opStar_conj_mem ((normalizer (Y : Set G)).inv_mem hgY) hx)
  have hAL := (IH L hLX).1 S₀ hLp hS₀p hS₀L
  set L₁ : Subgroup G := OpStar p (L ⊓ centralizer (S₀ : Set G)) with hL₁
  have hcommK : ⁅L, S₀⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro l hl s hs
    have hlX : l ∈ X := (opStar_le p Y hl).1
    have hsK : s ∈ K := hSK hs.1
    have h1 : l * s * l⁻¹ ∈ K := by
      have hn := opStarP_normal p X
      have := hn.conj_mem ⟨s, opStarP_le p X hsK⟩ hsK ⟨l, hlX⟩
      exact this
    have : ⁅l, s⁆ = (l * s * l⁻¹) * s⁻¹ := by rw [commutatorElement_def]
    rw [this]
    exact K.mul_mem h1 (K.inv_mem hsK)
  have hL₁K : ¬ L₁ ≤ K := by
    intro h
    exact hLK (hAL.trans (sup_le hcommK h))
  have hL₁le : L₁ ≤ OpStar p (X ⊓ centralizer ((S₀ ⊔ P : Subgroup G) : Set G)) := by
    set Z' : Subgroup G := X ⊓ centralizer ((S₀ ⊔ P : Subgroup G) : Set G) with hZ'
    have hL₁sub : L ⊓ centralizer (S₀ : Set G) ≤ Z' := by
      intro x hx
      refine ⟨(opStar_le p Y hx.1).1, ?_⟩
      rw [centralizer_sup_eq]
      exact ⟨hx.2, (opStar_le p Y hx.1).2⟩
    have hL₁Z : L₁ ≤ Z' := (opStar_le p _).trans hL₁sub
    have hnormZ : (L₁.subgroupOf Z').Normal := by
      refine normal_subgroupOf_of_conj fun g hg x hx => ?_
      have hg' : g ∈ X ⊓ centralizer (P : Set G) ⊓ centralizer (S₀ : Set G) := by
        refine ⟨⟨hg.1, ?_⟩, ?_⟩
        · exact (centralizer_sup_eq.le hg.2).2
        · exact (centralizer_sup_eq.le hg.2).1
      have hgY : g ∈ normalizer (Y : Set G) := Subgroup.le_normalizer hg'.1
      have hgL : g ∈ normalizer (L : Set G) := by
        refine mem_normalizer_of_conj (fun x hx => opStar_conj_mem hgY hx) (fun x hx =>
          opStar_conj_mem ((normalizer (Y : Set G)).inv_mem hgY) hx)
      have hgC : g ∈ normalizer ((centralizer (S₀ : Set G) : Subgroup G) : Set G) :=
        Subgroup.le_normalizer hg'.2
      have hgLC : g ∈ normalizer ((L ⊓ centralizer (S₀ : Set G) : Subgroup G) : Set G) :=
        mem_normalizer_inf hgL hgC
      exact opStar_conj_mem hgLC hx
    exact le_opStar hL₁Z hnormZ (isPStar_opStar h56 _)
  have hSP : S₀ ⊔ P ≤ normalizer (X : Set G) := by
    refine sup_le (fun g hg => ?_) hPn
    exact Subgroup.le_normalizer (opStarP_le p X (hSK hg.1))
  have hSPp : IsPGroup p ↥(S₀ ⊔ P) :=
    isPGroup_sup_of_le_normalizer hS₀p hP (fun g hg => hg.2)
  have hbad : ¬ OpStar p (X ⊓ centralizer ((S₀ ⊔ P : Subgroup G) : Set G)) ≤ OpStar p X := by
    intro h
    exact hL₁K ((hL₁le.trans h).trans (opStar_le_opStarP p X))
  have hmax : Nat.card (S₀ ⊔ P : Subgroup G) ≤ Nat.card P :=
    hPmax _ ⟨hSPp, hSP, hbad⟩
  have hS₀P : S₀ ≤ P := by
    have hPSP : P ≤ S₀ ⊔ P := le_sup_right
    have : S₀ ⊔ P = P := (Subgroup.eq_of_le_of_card_ge hPSP hmax).symm
    exact le_sup_left.trans this.le
  have hSP' : S ≤ P := le_of_inf_normalizer_le hP hSp hPS hS₀P
  have hLC : L ≤ X ⊓ centralizer (S : Set G) := by
    intro x hx
    have hxY : x ∈ Y := opStar_le p Y hx
    exact ⟨hxY.1, (Subgroup.centralizer_le fun t ht => hSP' ht) hxY.2⟩
  exact hLK ((hLC.trans (h59 G X S hS)))

theorem propA (h52i : BenderL52i p) (h52ii : BenderL52ii p) (h53 : BenderL53 p) (h54 : BenderL54 p)
    (h55 : BenderL55 p) (h56 : BenderL56 p) {X : Subgroup G}
    (IH : ∀ Y : Subgroup G, Nat.card Y < Nat.card X → PropA p Y ∧ PropB p Y) : PropA p X := by
  intro P hX hP hPn
  by_cases hcent : X ≤ centralizer (P : Set G)
  · rw [inf_eq_left.2 hcent, opStar_eq_self hX]
    exact le_sup_right
  set N : Subgroup G := ⁅X, P⁆ with hN
  have hNX : N ≤ X := commutator_le_of_le_normalizer hPn
  have hNn : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 (le_normalizer_commutator hPn).1
  have hPN : P ≤ normalizer (N : Set G) := (le_normalizer_commutator hPn).2
  obtain ⟨T, hT, hPT⟩ := exists_invariant_sylow hP hPN
  set C : Subgroup G := X ⊓ centralizer (T : Set G) with hC
  set X₁ : Subgroup G := oResOf p C with hX₁
  have hX₁p : IsPStar p ↥X₁ := h54 G X N T hX hNX hNn hT
  have hX₁X : X₁ ≤ X := (oResOf_le p C).trans inf_le_left
  have hdec : X ≤ N ⊔ X₁ := by
    have h1 : X ≤ N ⊔ C := fun y hy => by
      obtain ⟨n, hn, c, hc, rfl⟩ := hX.mul_centralizer hNX hNn hT y hy
      exact Subgroup.mul_mem_sup hn hc
    exact le_sup_oResOf_of_le_sup hNX hNn inf_le_left h1 hX.oResOf_eq
  rcases lt_or_eq_of_le hX₁X with hlt | heq
  ·
    obtain ⟨hA1, hB1⟩ := IH X₁ (Subgroup.card_lt_of_lt hlt)
    have hCn : ∀ g ∈ P, g ∈ normalizer (C : Set G) := fun g hg =>
      mem_normalizer_inf (hPn hg) (mem_normalizer_centralizer (hPT hg))
    have hPX₁ : P ≤ normalizer (X₁ : Set G) := fun g hg =>
      normalizer_le_normalizer_oResOf C (hCn g hg)
    have hAX₁ := hA1 P hX₁p hP hPX₁
    set X₂ : Subgroup G := OpStar p (X₁ ⊓ centralizer (P : Set G)) with hX₂
    have hX₂le : X₂ ≤ OpStar p (X ⊓ centralizer ((T ⊔ P : Subgroup G) : Set G)) := by
      set Z : Subgroup G := X ⊓ centralizer ((T ⊔ P : Subgroup G) : Set G) with hZ
      have hsub : X₁ ⊓ centralizer (P : Set G) ≤ Z := by
        intro x hx
        refine ⟨hX₁X hx.1, ?_⟩
        rw [centralizer_sup_eq]
        exact ⟨((oResOf_le p C) hx.1).2, hx.2⟩
      have hX₂Z : X₂ ≤ Z := (opStar_le p _).trans hsub
      have hnormZ : (X₂.subgroupOf Z).Normal := by
        refine normal_subgroupOf_of_conj fun g hg x hx => ?_
        have hgC : g ∈ C := ⟨hg.1, (centralizer_sup_eq.le hg.2).1⟩
        have hgP : g ∈ centralizer (P : Set G) := (centralizer_sup_eq.le hg.2).2
        have hgX₁ : g ∈ normalizer (X₁ : Set G) :=
          normalizer_le_normalizer_oResOf C (Subgroup.le_normalizer hgC)
        have hgCP : g ∈ normalizer ((centralizer (P : Set G) : Subgroup G) : Set G) :=
          Subgroup.le_normalizer hgP
        have hgW : g ∈ normalizer ((X₁ ⊓ centralizer (P : Set G) : Subgroup G) : Set G) :=
          mem_normalizer_inf hgX₁ hgCP
        exact opStar_conj_mem hgW hx
      exact le_opStar hX₂Z hnormZ (isPStar_opStar h56 _)
    have hTP : IsPGroup p ↥(T ⊔ P) := by
      have := isPGroup_sup_of_le_normalizer hP hT.2.1 hPT
      rwa [sup_comm] at this
    have hTPn : T ⊔ P ≤ normalizer (X : Set G) :=
      sup_le (fun g hg => Subgroup.le_normalizer (hNX (hT.1 hg))) hPn
    have hchain := chain_le (fun Y hY => (IH Y hY).2) (Nat.card (T ⊔ P : Subgroup G) - Nat.card P)
      P (T ⊔ P) rfl hTP le_sup_right hTPn hcent
    have hX₂C : X₂ ≤ OpStar p (X ⊓ centralizer (P : Set G)) := hX₂le.trans hchain
    calc X ≤ N ⊔ X₁ := hdec
      _ ≤ N ⊔ (⁅X₁, P⁆ ⊔ X₂) := sup_le_sup_left hAX₁ N
      _ ≤ N ⊔ OpStar p (X ⊓ centralizer (P : Set G)) :=
        sup_le le_sup_left (sup_le ((Subgroup.commutator_mono hX₁X le_rfl).trans le_sup_left)
          (hX₂C.trans le_sup_right))
  ·
    have hXC : X ≤ centralizer (T : Set G) := fun x hx => by
      have : x ∈ X₁ := by rw [heq]; exact hx
      exact ((oResOf_le p C) this).2
    set X₂ : Subgroup G := oResOf p (X ⊓ centralizer (P : Set G)) with hX₂
    have hX₂X : X₂ ≤ X := (oResOf_le p _).trans inf_le_left
    have hdecA : X = ⁅X, P⁆ ⊔ X₂ := h55 G X P hX hP hPn
    have hXN : X ≤ N ⊔ X₂ := hdecA.le
    set N₂ : Subgroup G := N ⊓ X₂ with hN₂
    have hN₂n : (N₂.subgroupOf X₂).Normal := normal_inf_subgroupOf hNX hNn hX₂X
    obtain ⟨T₂, hT₂⟩ := exists_isSylowIn p N₂
    have hTc : ∀ t ∈ T, ∀ n ∈ N, t * n = n * t := fun t ht n hn =>
      mem_centralizer_iff.mp (hXC (hNX hn)) t ht
    have hcopN : Nat.Coprime p (Nat.card (oResOf p N)) :=
      coprime_card_oResOf_of_central_sylow hT hTc
    have hII : IsPStar p ↥(oResOf p N₂) := by
      refine h52i ↥(oResOf p N₂) ?_
      have hdvd : Nat.card (oResOf p N₂) ∣ Nat.card (oResOf p N) :=
        Subgroup.card_dvd_of_le (oResOf_mono inf_le_left)
      exact Nat.Coprime.coprime_dvd_right hdvd hcopN
    have hTT₂ : T₂ ≤ T := by
      have hT₂N : T₂ ≤ N := hT₂.1.trans inf_le_left
      have hTn : T₂ ≤ normalizer (T : Set G) := fun g hg =>
        Subgroup.centralizer_le_normalizer (T : Set G) (hXC (hNX (hT₂N hg)))
      have hsup : IsPGroup p ↥(T₂ ⊔ T) := isPGroup_sup_of_le_normalizer hT₂.2.1 hT.2.1 hTn
      have hle : Nat.card (T₂ ⊔ T : Subgroup G) ≤ Nat.card T :=
        hT.2.2 _ (sup_le hT₂N hT.1) hsup
      have : T₂ ⊔ T = T := (Subgroup.eq_of_le_of_card_ge le_sup_right hle).symm
      exact le_sup_left.trans this.le
    have hiii : oResOf p X₂ ≤ oResOf p N₂ ⊔ (X₂ ⊓ centralizer (T₂ : Set G)) := by
      refine (oResOf_le p X₂).trans ?_
      refine le_trans (le_inf le_rfl ?_) le_sup_right
      intro x hx
      exact (Subgroup.centralizer_le fun t ht => hTT₂ ht) (hXC (hX₂X hx))
    have hquot : IsPStar p (↥X₂ ⧸ N₂.subgroupOf X₂) :=
      isPStar_quot_of_le_sup hNX hNn hX₂X hXN (h52ii _ _ hX)
    have hX₂p' := h53 G X₂ N₂ T₂ inf_le_right hT₂ hquot hII hiii
    have hX₂p : IsPStar p ↥X₂ := by
      have e : oResOf p X₂ = X₂ := oResOf_oResOf p _
      rwa [e] at hX₂p'
    have hX₂le : X₂ ≤ OpStar p (X ⊓ centralizer (P : Set G)) :=
      le_opStar (oResOf_le p _) (oResOf_normal p _) hX₂p
    calc X = ⁅X, P⁆ ⊔ X₂ := hdecA
      _ ≤ ⁅X, P⁆ ⊔ OpStar p (X ⊓ centralizer (P : Set G)) := sup_le_sup_left hX₂le _

theorem propAB (h52i : BenderL52i p) (h52ii : BenderL52ii p) (h53 : BenderL53 p) (h54 : BenderL54 p)
    (h55 : BenderL55 p) (h56 : BenderL56 p) (h59 : BenderT59 p) :
    ∀ n : ℕ, ∀ X : Subgroup G, Nat.card X ≤ n → PropA p X ∧ PropB p X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hX
    have IH : ∀ Y : Subgroup G, Nat.card Y < Nat.card X → PropA p Y ∧ PropB p Y :=
      fun Y hY => ih (Nat.card Y) (lt_of_lt_of_le hY hX) Y le_rfl
    exact ⟨propA h52i h52ii h53 h54 h55 h56 IH, propB h56 h59 IH⟩

omit [Finite G] [Fact p.Prime] in
theorem sup_commutator_opStar_le (p : ℕ) (X P : Subgroup G) (hPn : P ≤ normalizer (X : Set G)) :
    ⁅X, P⁆ ⊔ OpStar p (X ⊓ centralizer (P : Set G)) ≤ X :=
  sup_le (commutator_le_of_le_normalizer hPn) ((opStar_le p _).trans inf_le_left)

theorem bender_t510 (h52i : BenderL52i p) (h52ii : BenderL52ii p) (h53 : BenderL53 p) (h54 : BenderL54 p)
    (h55 : BenderL55 p) (h56 : BenderL56 p) (h59 : BenderT59 p) : BenderT510 p := by
  intro G _ _ X P hX hP hPn
  exact le_antisymm ((propAB h52i h52ii h53 h54 h55 h56 h59 _ X le_rfl).1 P hX hP hPn)
    (sup_commutator_opStar_le p X P hPn)

theorem bender_t511 (h52i : BenderL52i p) (h52ii : BenderL52ii p) (h53 : BenderL53 p) (h54 : BenderL54 p)
    (h55 : BenderL55 p) (h56 : BenderL56 p) (h59 : BenderT59 p) : BenderT511 p := by
  intro G _ _ X P hP hPn
  exact (propAB h52i h52ii h53 h54 h55 h56 h59 _ X le_rfl).2 P hP hPn

end CFSG.GH74.GLS.Balance

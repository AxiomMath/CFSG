
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Gen

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Kc3J4 CFSG.QuasithinUnique.A5.Kc3Gen
open scoped Pointwise commutatorElement

@[expose] def InvRadical (X : Type*) [Group X] : Prop :=
  ∀ y : X, y * y = 1 → y ≠ 1 → ∃ N : Subgroup X, IsPGroup 2 N ∧ y ∈ N ∧
    N ≤ Subgroup.centralizer ({y} : Set X) ∧
    (∀ q ∈ Subgroup.centralizer ({y} : Set X), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
    (∀ q ∈ Subgroup.centralizer ({y} : Set X), (∀ e ∈ N, q * e = e * q) → q ∈ N) ∧
    ∀ g ∈ Subgroup.centralizer ({y} : Set X), orderOf g = 5 →
      16 < (N ⊓ Subgroup.centralizer ({g} : Set X)).relIndex N

@[expose] def InvRadicalIn {G : Type*} [Group G] (K : Subgroup G) : Prop :=
  ∀ y ∈ K, orderOf y = 2 → ∃ N : Subgroup G, N ≤ K ∧ IsPGroup 2 N ∧ y ∈ N ∧
    N ≤ Subgroup.centralizer ({y} : Set G) ∧
    (∀ q ∈ K ⊓ Subgroup.centralizer ({y} : Set G), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
    (∀ q ∈ K ⊓ Subgroup.centralizer ({y} : Set G), (∀ e ∈ N, q * e = e * q) → q ∈ N) ∧
    ∀ g ∈ K ⊓ Subgroup.centralizer ({y} : Set G), orderOf g = 5 →
      16 < (N ⊓ Subgroup.centralizer ({g} : Set G)).relIndex N

section Transport

theorem invRadicalIn_of_invRadical {G : Type*} [Group G] {K : Subgroup G}
    (h : InvRadical ↥K) : InvRadicalIn K := by
  intro y hyK hyo
  have hy2 : y * y = 1 := by
    rw [← pow_two, ← hyo]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    simp at hyo
  obtain ⟨N', hN2, hyN, hNc, hKN, hself, hnum⟩ := h ⟨y, hyK⟩ (Subtype.ext (by simpa using hy2))
    (fun h1 => hy1 (congrArg Subtype.val h1))
  have hf : Function.Injective K.subtype := K.subtype_injective
  refine ⟨N'.map K.subtype, Subgroup.map_subtype_le _, hN2.of_equiv (N'.equivMapOfInjective _ hf),
    ⟨_, hyN, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hNc hn)
    exact congrArg Subtype.val this
  · rintro q ⟨hqK, hqc⟩ _ ⟨e, he, rfl⟩
    have hq' : (⟨q, hqK⟩ : ↥K) ∈ Subgroup.centralizer ({(⟨y, hyK⟩ : ↥K)} : Set ↥K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hqc)
    exact ⟨_, hKN _ hq' e he, rfl⟩
  · rintro q ⟨hqK, hqc⟩ hqe
    have hq' : (⟨q, hqK⟩ : ↥K) ∈ Subgroup.centralizer ({(⟨y, hyK⟩ : ↥K)} : Set ↥K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hqc)
    have := hself _ hq' (fun e he => Subtype.ext (hqe e ⟨e, he, rfl⟩))
    exact ⟨_, this, rfl⟩
  · rintro g ⟨hgK, hgc⟩ hg5
    have hg' : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.centralizer ({(⟨y, hyK⟩ : ↥K)} : Set ↥K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hgc)
    have hg5' : orderOf (⟨g, hgK⟩ : ↥K) = 5 := by
      rw [← hg5, ← Subgroup.orderOf_coe]
    have key := hnum _ hg' hg5'
    have heq : N'.map K.subtype ⊓ Subgroup.centralizer ({g} : Set G) =
        (N' ⊓ Subgroup.centralizer ({(⟨g, hgK⟩ : ↥K)} : Set ↥K)).map K.subtype := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨⟨n, hn, rfl⟩, hxc⟩
        refine ⟨n, Subgroup.mem_inf.2 ⟨hn, ?_⟩, rfl⟩
        have := Subgroup.mem_centralizer_singleton_iff.1 hxc
        exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext this)
      · rintro ⟨n, hn, rfl⟩
        obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
        refine ⟨⟨n, hn1, rfl⟩, ?_⟩
        have := Subgroup.mem_centralizer_singleton_iff.1 hn2
        exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
    rw [heq, Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact key

theorem invRadical_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : InvRadical X) :
    InvRadical Y := by
  intro y hy2 hy1
  obtain ⟨N, hN2, hyN, hNc, hKN, hself, hnum⟩ := h (e.symm y) (by
    apply e.injective
    simp [hy2]) (fun h1 => hy1 (by simpa using congrArg e h1))
  have hf : Function.Injective e.toMonoidHom := e.injective
  have hcent : ∀ (a b : X), a * b = b * a ↔ e a * e b = e b * e a := fun a b => by
    rw [← map_mul, ← map_mul]
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  refine ⟨N.map e.toMonoidHom, hN2.of_equiv (N.equivMapOfInjective _ hf), ⟨_, hyN, by simp⟩, ?_,
    ?_, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hNc hn)
    have h2 := (hcent _ _).1 this
    simpa using h2
  · rintro q hq _ ⟨n, hn, rfl⟩
    have hq' : e.symm q ∈ Subgroup.centralizer ({e.symm y} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hq ⊢
      have := (hcent (e.symm q) (e.symm y)).2 (by simpa using hq)
      exact this
    refine ⟨_, hKN _ hq' n hn, ?_⟩
    simp
  · intro q hq hqe
    have hq' : e.symm q ∈ Subgroup.centralizer ({e.symm y} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hq ⊢
      have := (hcent (e.symm q) (e.symm y)).2 (by simpa using hq)
      exact this
    have := hself _ hq' (fun n hn => by
      have := hqe (e n) ⟨n, hn, rfl⟩
      apply e.injective
      simpa using this)
    exact ⟨_, this, by simp⟩
  · intro g hg hg5
    have hg' : e.symm g ∈ Subgroup.centralizer ({e.symm y} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      have := (hcent (e.symm g) (e.symm y)).2 (by simpa using hg)
      exact this
    have hg5' : orderOf (e.symm g) = 5 := by rw [e.symm.orderOf_eq]; exact hg5
    have key := hnum _ hg' hg5'
    have heq : N.map e.toMonoidHom ⊓ Subgroup.centralizer ({g} : Set Y) =
        (N ⊓ Subgroup.centralizer ({e.symm g} : Set X)).map e.toMonoidHom := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨⟨n, hn, rfl⟩, hxc⟩
        refine ⟨n, Subgroup.mem_inf.2 ⟨hn, ?_⟩, rfl⟩
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hxc
        have := (hcent n (e.symm g)).2 (by simpa using h1)
        exact Subgroup.mem_centralizer_singleton_iff.2 this
      · rintro ⟨n, hn, rfl⟩
        obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
        refine ⟨⟨n, hn1, rfl⟩, ?_⟩
        have := (hcent n (e.symm g)).1 (Subgroup.mem_centralizer_singleton_iff.1 hn2)
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        simpa using this
    rw [heq, Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact key

end Transport

theorem relIndex_inf_mono {G : Type*} [Group G] [Finite G] {N R : Subgroup G} (hNR : N ≤ R)
    (g : G) : (N ⊓ Subgroup.centralizer ({g} : Set G)).relIndex N ≤
      (R ⊓ Subgroup.centralizer ({g} : Set G)).relIndex R := by
  have : (Subgroup.centralizer ({g} : Set G)).IsFiniteRelIndex R :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have h1 := Subgroup.relIndex_le_of_le_right (H := Subgroup.centralizer ({g} : Set G)) hNR
    Subgroup.relIndex_ne_zero
  have e1 : (N ⊓ Subgroup.centralizer ({g} : Set G)).relIndex N =
      (Subgroup.centralizer ({g} : Set G)).relIndex N := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right _ _
  have e2 : (R ⊓ Subgroup.centralizer ({g} : Set G)).relIndex R =
      (Subgroup.centralizer ({g} : Set G)).relIndex R := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right _ _
  rw [e1, e2]
  exact h1

theorem kc3_core {G : Type} [Group G] [Finite G] {K L S₀ T₀ : Subgroup G}
    (hK5 : ¬ 5 ^ 2 ∣ Nat.card K) (hLK : L ≤ K) (hL : D5Plus L) (hLp : ⁅L, L⁆ = L)
    (hSL : S₀ ≤ Subgroup.normalizer (L : Set G)) (hS : IsPGroup 2 S₀) (hT : IsPGroup 2 T₀)
    (hST : S₀ ≤ T₀) (hTK : T₀ ≤ Subgroup.normalizer (K : Set G))
    (hMC : ∃ y ∈ K, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l) (hIR : InvRadicalIn K) :
    ∃ X S₁ : Subgroup G, CharTwo X ∧ L ⊔ S₀ ≤ X ∧ X ≤ K ⊔ T₀ ∧ IsSylowTwoOf S₁ X ∧ S₀ ≤ S₁ ∧
      ¬ IsSubnormal L (L ⊔ S₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, hQLV, α, hα, hαQ, β, hβ⟩ := hL
  obtain ⟨y0, hy0K, hy0o, hy0c⟩ := hMC
  have hSK : S₀ ≤ Subgroup.normalizer (K : Set G) := hST.trans hTK
  set C : Subgroup G := K ⊓ Subgroup.centralizer (L : Set G) with hC
  have hSC : S₀ ≤ Subgroup.normalizer (C : Set G) := by
    refine le_normalizer_of_conj_mem fun s hs c hc => ?_
    obtain ⟨hcK, hcC⟩ := hc
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hSK hs) c).1 hcK, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro l hl
    have hl' : s⁻¹ * l * s ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (hSL (S₀.inv_mem hs)) l).1 hl
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hcC _ hl'
    calc l * (s * c * s⁻¹) = s * ((s⁻¹ * l * s) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * l * s)) * s⁻¹ := by rw [h1]
      _ = (s * c * s⁻¹) * l := by group
  obtain ⟨y, hyC, hyo, hyfix⟩ := exists_fixed_involution hS hSC
    ⟨y0, ⟨hy0K, Subgroup.mem_centralizer_iff.2 hy0c⟩, hy0o⟩
  have hyK : y ∈ K := hyC.1
  have hyL : ∀ l ∈ L, l * y = y * l := Subgroup.mem_centralizer_iff.1 hyC.2
  obtain ⟨N, hNK, hN2, hyN, hNc, hKN, hself, hnum⟩ := hIR y hyK hyo
  set D : Subgroup G := K ⊓ Subgroup.centralizer ({y} : Set G) with hD
  set R : Subgroup G := pCoreOf 2 D with hR
  have hND : N ≤ D := le_inf hNK hNc
  have hDN : D ≤ Subgroup.normalizer (N : Set G) := le_normalizer_of_conj_mem hKN
  have hNR : N ≤ R := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hND hDN hN2
  have hRD : R ≤ D := CFSG.LieType.BorelTits.pCoreOf_le 2 D
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D
  have hDR : D ≤ Subgroup.normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D
  have hRK : R ≤ K := hRD.trans inf_le_left
  have hyR : y ∈ R := hNR hyN
  have hCR : K ⊓ Subgroup.centralizer (R : Set G) ≤ R := by
    rintro c ⟨hcK, hcR⟩
    have hcy : c ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.1 hcR) y hyR).symm
    have hcN : ∀ e ∈ N, c * e = e * c := fun e he =>
      ((Subgroup.mem_centralizer_iff.1 hcR) e (hNR he)).symm
    exact hNR (hself c ⟨hcK, hcy⟩ hcN)
  have hLD : L ≤ D := le_inf hLK (fun l hl => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hyL l hl)
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := hLD.trans hDR
  have hconjD : ∀ s ∈ S₀, ∀ d ∈ D, s * d * s⁻¹ ∈ D := by
    intro s hs d hd
    obtain ⟨hdK, hdc⟩ := hd
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hSK hs) d).1 hdK, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hdc
    have h2 := hyfix s hs
    calc s * d * s⁻¹ * y = s * d * s⁻¹ * (s * y * s⁻¹) := by rw [h2]
      _ = s * (d * y) * s⁻¹ := by group
      _ = s * (y * d) * s⁻¹ := by rw [h1]
      _ = (s * y * s⁻¹) * (s * d * s⁻¹) := by group
      _ = y * (s * d * s⁻¹) := by rw [h2]
  have hSR : S₀ ≤ Subgroup.normalizer (R : Set G) := by
    refine le_normalizer_of_conj_mem fun s hs r hr => ?_
    let f : G ≃* G := MulAut.conj s
    have hDf : D.map f.toMonoidHom = D := by
      apply le_antisymm
      · rintro _ ⟨d, hd, rfl⟩
        exact hconjD s hs d hd
      · intro x hx
        refine ⟨s⁻¹ * x * s, ?_, ?_⟩
        · simpa using hconjD s⁻¹ (S₀.inv_mem hs) x hx
        · simp [f, MulAut.conj_apply, mul_assoc]
    have h1 := pCoreOf_map_equiv 2 f D
    rw [hDf] at h1
    have h2 : f r ∈ R.map f.toMonoidHom := ⟨r, hr, rfl⟩
    have h3 : R.map f.toMonoidHom = R := h1.symm
    rw [h3] at h2
    simpa [f, MulAut.conj_apply] using h2
  have hcharTwo : CharTwo ((K ⊔ T₀) ⊓ Subgroup.normalizer (R : Set G)) :=
    charTwo_normalizer hT hTK hR2 hRK hCR
  set X : Subgroup G := (K ⊔ T₀) ⊓ Subgroup.normalizer (R : Set G) with hX
  have hLSX : L ⊔ S₀ ≤ X :=
    sup_le (le_inf (hLK.trans le_sup_left) hLR) (le_inf (hST.trans le_sup_right) hSR)
  have hRX : R ≤ X := le_inf (hRK.trans le_sup_left) Subgroup.le_normalizer
  obtain ⟨S₁, hSS₁, hS₁⟩ := exists_sylowTwoOf_le (le_sup_right.trans hLSX) hS
  refine ⟨X, S₁, hcharTwo, hLSX, inf_le_left, hS₁, hSS₁, ?_⟩
  intro hsub
  have hL25 : ¬ 5 ^ 2 ∣ Nat.card L := fun h => hK5 (h.trans (Subgroup.card_dvd_of_le hLK))
  have hLS₁ : L ⊔ S₁ ≤ K ⊔ T₀ := sup_le (hLK.trans le_sup_left) (hS₁.1.trans inf_le_left)
  have hY : ¬ 5 ^ 2 ∣ Nat.card ↥(L ⊔ S₁) :=
    not_prime_sq_dvd_of_le_sup (p := 5) (by norm_num) hT hTK hLS₁ hK5
  have hgen : ∀ N' : Subgroup G, (∀ x ∈ L, orderOf x = 5 → x ∈ N') → L ≤ N' := fun N' h =>
    le_of_five_elements hQ2 hQL α hα hαQ hLp h
  have hnorm := normalizes_of_isSubnormal (p := 5) hsub (five_dvd_card α hα) hY hgen
  have hS₁L : S₁ ≤ Subgroup.normalizer (L : Set G) := le_sup_right.trans hnorm
  have hRS₁ : R ≤ S₁ := le_of_normalizes_isSylowTwoOf hS₁ hRX inf_le_right hR2
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRS₁.trans hS₁L
  obtain ⟨g, hgL, hg5⟩ := exists_orderOf_five α hα
  have hmax : ∀ D' : Subgroup G, D' ≤ L → L ≤ Subgroup.normalizer (D' : Set G) →
      IsPGroup 2 D' → D' ≤ Q := fun D' h1 h2 h3 => le_Q_of_normal_two α hα hαQ h1 h2 h3
  have h1 := relIndex_centralizer_le hgL hg5 hL25 hQL hLQ hQ2 hmax hQLV hR2 hRL hLR
  have hV : Nat.card V = 16 := card_V β
  have h2 := hnum g (hLD hgL) hg5
  have h3 := relIndex_inf_mono hNR g
  omega

end CFSG.QuasithinUnique.A5

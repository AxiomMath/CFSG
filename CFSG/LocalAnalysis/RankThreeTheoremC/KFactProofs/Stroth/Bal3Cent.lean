module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Sec
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Elem
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

section Generic

theorem centralizer_zpowers_eq_singleton {G : Type*} [Group G] (g : G) :
    centralizer ((zpowers g : Subgroup G) : Set G) = centralizer ({g} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem disjoint_of_le_centralizer {X : Type*} [Group X] {K L : Subgroup X}
    (hZ : center K = ⊥) (hL : L ≤ centralizer (K : Set X)) : Disjoint K L := by
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxK, hxL⟩
  have h : (⟨x, hxK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 (hL hxL) (g : X) g.2)
  rw [hZ, mem_bot] at h
  exact mem_bot.2 (congrArg Subtype.val h)

theorem le_centralizer_of_ne_component {X : Type*} [Group X] [Finite X] {K L : Subgroup X}
    (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤) (h : K ≠ L) :
    K ≤ centralizer (L : Set X) :=
  commutator_eq_bot_iff_le_centralizer.mp
    (ComponentClassification.LocalComponents.commute_of_ne K L hK hL h)

end Generic

section Product

theorem noSimpleSec_centralizer_prod {P Q : Type*} [Group P] [Group Q] {p : ℕ} (u : P) (v : Q)
    (hu : NoSimpleSec p (centralizer ({u} : Set P)))
    (hv : NoSimpleSec p (centralizer ({v} : Set Q))) :
    NoSimpleSec p (centralizer ({(u, v)} : Set (P × Q))) := by
  have h : centralizer ({(u, v)} : Set (P × Q)) =
      (centralizer ({u} : Set P)).prod (centralizer ({v} : Set Q)) := by
    ext ⟨a, b⟩
    simp [mem_centralizer_iff, Subgroup.mem_prod, Prod.ext_iff]
  rw [h]
  exact NoSimpleSec.of_mulEquiv (Subgroup.prodEquiv _ _) (NoSimpleSec.prod hu hv)

theorem noSimpleSec_centralizer_inf_range {P X : Type*} [Group P] [Group X] {p : ℕ} (ψ : P →* X)
    (hψ : Function.Injective ψ) (u : P) (hu : NoSimpleSec p (centralizer ({u} : Set P))) :
    NoSimpleSec p ↥(centralizer ({ψ u} : Set X) ⊓ ψ.range) := by
  have h : centralizer ({ψ u} : Set X) ⊓ ψ.range = (centralizer ({u} : Set P)).map ψ := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hx, a, rfl⟩
      refine ⟨a, ?_, rfl⟩
      have h1 : ψ u * ψ a = ψ a * ψ u := mem_centralizer_iff.1 hx (ψ u) (Set.mem_singleton _)
      rw [← map_mul, ← map_mul] at h1
      simpa [mem_centralizer_iff] using hψ h1
    · rintro ⟨a, ha, rfl⟩
      refine ⟨?_, a, rfl⟩
      rw [mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have h1 : u * a = a * u := mem_centralizer_iff.1 ha u (Set.mem_singleton _)
      rw [← map_mul, ← map_mul, h1]
  rw [h]
  exact NoSimpleSec.of_mulEquiv ((centralizer ({u} : Set P)).equivMapOfInjective ψ hψ).symm hu

theorem exists_injective_prod_three {X : Type*} [Group X] {K₁ K₂ K₃ : Subgroup X}
    (h₁₂ : K₂ ≤ centralizer (K₁ : Set X)) (h₁₃ : K₃ ≤ centralizer (K₁ : Set X))
    (h₂₃ : K₃ ≤ centralizer (K₂ : Set X)) (hZ₁ : center K₁ = ⊥) (hZ₂ : center K₂ = ⊥) :
    ∃ ψ : K₁ × (K₂ × K₃) →* X, Function.Injective ψ ∧ ψ.range = K₁ ⊔ K₂ ⊔ K₃ ∧
      ∀ (a : K₁) (b : K₂) (c : K₃), ψ (a, (b, c)) = (a : X) * ((b : X) * (c : X)) := by
  have hc₂₃ : ∀ (m : K₂) (n : K₃), Commute (K₂.subtype m) (K₃.subtype n) := fun m n =>
    mem_centralizer_iff.1 (h₂₃ n.2) (m : X) m.2
  have hψ₂range : (K₂.subtype.noncommCoprod K₃.subtype hc₂₃).range = K₂ ⊔ K₃ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hψ₂inj : Function.Injective (K₂.subtype.noncommCoprod K₃.subtype hc₂₃) := by
    refine (MonoidHom.noncommCoprod_injective _ _ _).2
      ⟨K₂.subtype_injective, K₃.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_of_le_centralizer hZ₂ h₂₃
  have hc : ∀ (m : K₁) (n : K₂ × K₃),
      Commute (K₁.subtype m) (K₂.subtype.noncommCoprod K₃.subtype hc₂₃ n) := by
    intro m n
    have h2 : (m : X) * (n.1 : X) = (n.1 : X) * m :=
      mem_centralizer_iff.1 (h₁₂ n.1.2) (m : X) m.2
    have h3 : (m : X) * (n.2 : X) = (n.2 : X) * m :=
      mem_centralizer_iff.1 (h₁₃ n.2.2) (m : X) m.2
    show (m : X) * ((n.1 : X) * (n.2 : X)) = ((n.1 : X) * (n.2 : X)) * m
    rw [← mul_assoc, h2, mul_assoc, h3, mul_assoc]
  refine ⟨K₁.subtype.noncommCoprod (K₂.subtype.noncommCoprod K₃.subtype hc₂₃) hc, ?_, ?_,
    fun a b c => rfl⟩
  · refine (MonoidHom.noncommCoprod_injective _ _ _).2 ⟨K₁.subtype_injective, hψ₂inj, ?_⟩
    rw [Subgroup.range_subtype, hψ₂range]
    exact disjoint_of_le_centralizer hZ₁ (sup_le h₁₂ h₁₃)
  · rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, hψ₂range, sup_assoc]

end Product

section Component

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem isSCp_zpowers_of_components (hp : p.Prime) (hodd : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (hr : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    {K L M : Subgroup X} (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤)
    (hM : IsComponentOf M ⊤) (hKL : K ≠ L) (hKM : K ≠ M) (hLM : L ≠ M) {k : K}
    (hk : orderOf k = p) :
    CFSG.LocalAnalysis.GLTheoremB.IsSCp p (⊤ : Subgroup K) (zpowers k) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hkp : k ^ p = 1 := hk ▸ pow_orderOf_eq_one k
  refine ⟨le_top, CFSG.Open.isElemAbelian_zpowers hkp, ?_⟩
  intro E' _ hE' hle
  set A : Subgroup X := E'.map K.subtype with hAdef
  have hA : CFSG.Open.IsElemAbelian p A := CFSG.Open.IsElemAbelian.map hE' K.subtype
  obtain ⟨a, ha⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE').exists_card_eq
  have hAcard : Nat.card A = p ^ a := by
    rw [hAdef, Subgroup.card_subtype]
    exact ha
  have hAK : A ≤ K := Subgroup.map_subtype_le E'
  have hAL : A ≤ centralizer (L : Set X) := hAK.trans (le_centralizer_of_ne_component hK hL hKL)
  have hAM : A ≤ centralizer (M : Set X) := hAK.trans (le_centralizer_of_ne_component hK hM hKM)
  have hS : ∀ J ∈ ({L, M} : Finset (Subgroup X)), IsComponentOf J ⊤ := by
    intro J hJ
    rcases Finset.mem_insert.1 hJ with h | h
    · rw [h]; exact hL
    · rw [Finset.mem_singleton.1 h]; exact hM
  have hAC : ∀ J ∈ ({L, M} : Finset (Subgroup X)), A ≤ centralizer (J : Set X) := by
    intro J hJ
    rcases Finset.mem_insert.1 hJ with h | h
    · rw [h]; exact hAL
    · rw [Finset.mem_singleton.1 h]; exact hAM
  have h2 := card_add_le_pRank_of_components hp hodd hcore {L, M} hS hA hAcard hAC
  rw [Finset.card_pair hLM] at h2
  have ha1 : a ≤ 1 := by omega
  have hcardE : Nat.card E' ≤ p := by
    rw [ha]
    calc p ^ a ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos ha1
      _ = p := pow_one p
  have hcardB : Nat.card (zpowers k) = p := by rw [Nat.card_zpowers, hk]
  exact (eq_of_le_of_card_ge hle (by rw [hcardB]; exact hcardE)).symm

theorem noSimpleSec_centralizer_of_components (hp : p.Prime) (hodd : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (hr : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    {K L M : Subgroup X} (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤)
    (hM : IsComponentOf M ⊤) (hKL : K ≠ L) (hKM : K ≠ M) (hLM : L ≠ M) {k : K}
    (hk : orderOf k = p) : NoSimpleSec p (centralizer ({k} : Set K)) := by
  have hB := isSCp_zpowers_of_components hp hodd hcore hr hK hL hM hKL hKM hLM hk
  have h := NoSimpleSec.of_hasNormalPComplement hp
    (HardMathSupport.Timmesfeld.ComponentBalance.hasNormalPComplement_centralizer_of_isSCp
      hp hodd hB)
  rwa [centralizer_zpowers_eq_singleton] at h

end Component

theorem noSimpleSec_centralizer_inf_layer {X : Type} [Group X] [Finite X]
    (hcore : CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 3 = ⊥)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    {K₁ K₂ K₃ : Subgroup X}
    (h₁ : CFSG.Open.IsComponentOf K₁ ⊤) (h₂ : CFSG.Open.IsComponentOf K₂ ⊤)
    (h₃ : CFSG.Open.IsComponentOf K₃ ⊤)
    (h₁₂ : K₁ ≠ K₂) (h₁₃ : K₁ ≠ K₃) (h₂₃ : K₂ ≠ K₃)
    (hZ₁ : Subgroup.center K₁ = ⊥) (hZ₂ : Subgroup.center K₂ = ⊥)
    (hZ₃ : Subgroup.center K₃ = ⊥)
    {w : X} (hwE : w ∈ K₁ ⊔ K₂ ⊔ K₃) (hwo : orderOf w = 3)
    (hw₁ : w ∉ K₂ ⊔ K₃) (hw₂ : w ∉ K₁ ⊔ K₃) (hw₃ : w ∉ K₁ ⊔ K₂) :
    NoSimpleSec 3 ↥((Subgroup.centralizer ({w} : Set X)) ⊓ (K₁ ⊔ K₂ ⊔ K₃)) := by
  have hc₂₁ : K₂ ≤ centralizer (K₁ : Set X) := le_centralizer_of_ne_component h₂ h₁ h₁₂.symm
  have hc₃₁ : K₃ ≤ centralizer (K₁ : Set X) := le_centralizer_of_ne_component h₃ h₁ h₁₃.symm
  have hc₃₂ : K₃ ≤ centralizer (K₂ : Set X) := le_centralizer_of_ne_component h₃ h₂ h₂₃.symm
  obtain ⟨ψ, hψinj, hψrange, hψapp⟩ := exists_injective_prod_three hc₂₁ hc₃₁ hc₃₂ hZ₁ hZ₂
  have hwψ : w ∈ ψ.range := by rw [hψrange]; exact hwE
  obtain ⟨⟨a, b, c⟩, hψw⟩ := hwψ
  have hw3 : w ^ 3 = 1 := hwo ▸ pow_orderOf_eq_one w
  have hcube : (a, (b, c)) ^ 3 = 1 := by
    apply hψinj
    rw [map_pow, hψw, map_one]
    exact hw3
  have h3 : a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 := by
    simpa [Prod.ext_iff] using hcube
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hw₁
    rw [← hψw, hψapp, OneMemClass.coe_one, one_mul]
    exact Subgroup.mul_mem_sup b.2 c.2
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hw₂
    rw [← hψw, hψapp, OneMemClass.coe_one, one_mul]
    exact Subgroup.mul_mem_sup a.2 c.2
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hw₃
    rw [← hψw, hψapp, OneMemClass.coe_one, mul_one]
    exact Subgroup.mul_mem_sup a.2 b.2
  have ha : orderOf a = 3 := orderOf_eq_prime h3.1 ha1
  have hb : orderOf b = 3 := orderOf_eq_prime h3.2.1 hb1
  have hc : orderOf c = 3 := orderOf_eq_prime h3.2.2 hc1
  have hA : NoSimpleSec 3 (centralizer ({a} : Set K₁)) :=
    noSimpleSec_centralizer_of_components Nat.prime_three (by norm_num) hcore hr h₁ h₂ h₃
      h₁₂ h₁₃ h₂₃ ha
  have hB : NoSimpleSec 3 (centralizer ({b} : Set K₂)) :=
    noSimpleSec_centralizer_of_components Nat.prime_three (by norm_num) hcore hr h₂ h₁ h₃
      h₁₂.symm h₂₃ h₁₃ hb
  have hC : NoSimpleSec 3 (centralizer ({c} : Set K₃)) :=
    noSimpleSec_centralizer_of_components Nat.prime_three (by norm_num) hcore hr h₃ h₁ h₂
      h₁₃.symm h₂₃.symm h₁₂ hc
  have hu := noSimpleSec_centralizer_prod a (b, c) hA (noSimpleSec_centralizer_prod b c hB hC)
  have h := noSimpleSec_centralizer_inf_range ψ hψinj (a, (b, c)) hu
  rwa [hψw, hψrange] at h

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

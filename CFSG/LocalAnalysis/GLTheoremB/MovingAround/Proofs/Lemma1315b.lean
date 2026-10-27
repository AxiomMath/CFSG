module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop115

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple PQuot catalogIs)
open CFSG.LocalAnalysis.GLTheoremA (IsKHat)

@[expose] def Input23_19 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ B : Subgroup X, IsElemAbelian p B → 4 ≤ CFSG.Open.pRank p B →
      CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      ((∃ n : ℕ, IsAltType n (↥K ⧸ Subgroup.center ↥K)) ∨
        (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥K ⧸ Subgroup.center ↥K)) ∨
        (∀ A : Subgroup (MulAut ↥K), IsElemAbelian p A → CFSG.Open.pRank p A ≤ 2)) →
      K ≤ GLBCore p 2 B


@[expose] def Input3_3 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    GLAPPrimeCore p K = ⊥ → IsChevSimple 2 (K ⧸ Subgroup.center K) →
    IsChevSimple p (K ⧸ Subgroup.center K) → (p = 5 ∨ p = 7) ∧ IsLpType 2 p K

@[expose] def Input14_4_1 : Prop :=
  ∀ (p q : ℕ), p.Prime → 5 ≤ p → q.Prime → ∀ (K : Type) [Group K] [Finite K], IsKHat K →
    GLAPPrimeCore p K = ⊥ → IsChevSimple q (K ⧸ Subgroup.center K) →
    ∀ (J : Type) [Group J] (x : MulAut K), Lemma1314.PumpupVia p J K x →
      IsChevSimple q (J ⧸ Subgroup.center J) ∧ (q = p → x ∉ innerAut K)

@[expose] def Input14_18 : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (K : Type) [Group K] [Finite K], IsKHat K → GLAPPrimeCore p K = ⊥ →
    IsChevSimple p (K ⧸ Subgroup.center K) → ∀ (J : Type) [Group J] (x : MulAut K), IsLpType 2 p J →
      Lemma1314.PumpupVia p J K x → IsLpType 2 (p ^ p) K

@[expose] def Input25_5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → 5 ≤ p → CFSG.Open.IsKGroup Y →
    ∀ (K : Subgroup Y) (d : Y), IsComponentOf K ⊤ → d ∈ Subgroup.normalizer (K : Set Y) →
      orderOf d = p → (∃ name : TauCeti.SporadicName, IsSporType name (↥K ⧸ Subgroup.center ↥K)) →
      (∃ J : Subgroup Y, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set Y)) J ∧
        IsChevSimple 2 (PSimple p J)) →
      (∃ A : Subgroup Y, IsSCp p ⊤ A ∧ d ∈ A ∧ CFSG.Open.pRank p A = 3 ∧
        A ⊓ Subgroup.center Y ≠ ⊥) →
      ∀ B : Subgroup Y, IsEkIn p 4 ⊤ B → K ≤ GLBCore p 2 B

@[expose] def Input18_3DiagZ : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → ∀ x y : G, orderOf x = p → orderOf y = p →
    x * y = y * x → ∀ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x, y} : Set G)) J →
    ∀ L : ZMod p → Subgroup G, (∀ i, GLAPComponent p (Subgroup.centralizer ({y} : Set G)) (L i)) →
    Function.Injective L → (∀ i, GLBConj x (L i) = L (i + 1)) →
    (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) = ⨆ i, L i →
    ∀ i, Nonempty ((↥J ⧸ GLAPPrimeCore p ↥J) ⧸ Subgroup.center (↥J ⧸ GLAPPrimeCore p ↥J) ≃*
      (↥(L i) ⧸ GLAPPrimeCore p ↥(L i)) ⧸ Subgroup.center (↥(L i) ⧸ GLAPPrimeCore p ↥(L i)))

@[expose] def L2Facts (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  Subgroup.center K = ⊥ ∧
  (∀ S : Subgroup K, IsPGroup p S → IsElemAbelian p S ∧ Nat.card S ≤ p ^ p) ∧
  (∃ S : Subgroup K, IsPGroup p S ∧ Nat.card S = p ^ p) ∧
  (∀ E : Subgroup (MulAut K), IsElemAbelian p E →
    Nat.card E ≤ p ^ p ∧ (Nat.card E = p ^ p → E ≤ innerAut K)) ∧
  (∀ x : MulAut K, orderOf x = p → x ∉ innerAut K →
    ∀ S : Subgroup K, IsPGroup p S → (∀ s ∈ S, x s = s) → Nat.card S ≤ p) ∧
  (∀ S : Subgroup K, IsPGroup p S → Nat.card S = p →
    ∃ n ∈ Subgroup.normalizer (S : Set K), ∃ s ∈ S, n * s * n⁻¹ ≠ s)

@[expose] def InputL2 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K], IsLpType 2 (p ^ p) K → L2Facts p K


section Generic

variable {G : Type} [Group G]

theorem comm_of_mem {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem elemAbelian_mono {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (h : F ≤ E) :
    IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_of_mem hE (h a.2) (h b.2))⟩⟩, fun x hx => hE.2 x (h hx)⟩

theorem isPGroup_of_elemAbelian {p : ℕ} [Fact p.Prime] {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := fun g => ⟨1, by
  rw [pow_one]
  exact Subtype.ext (hE.2 g.1 g.2)⟩

theorem elemAbelian_sup {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hF : IsElemAbelian p F)
    (hEF : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a) : IsElemAbelian p (E ⊔ F) := by
  have hEC : E ≤ Subgroup.centralizer (F : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun f hf => (hEF e he f hf).symm
  have hEN : E ≤ Subgroup.normalizer (F : Set G) :=
    hEC.trans (Subgroup.centralizer_le_normalizer (F : Set G))
  have hmem : ∀ x ∈ E ⊔ F, ∃ e ∈ E, ∃ f ∈ F, x = e * f := by
    intro x hx
    have hx' : x ∈ ((E ⊔ F : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E F hEN] at hx'
    obtain ⟨e, he, f, hf, rfl⟩ := hx'
    exact ⟨e, he, f, hf, rfl⟩
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e, he, f, hf, ha⟩ := hmem a.1 a.2
    obtain ⟨e', he', f', hf', hb⟩ := hmem b.1 b.2
    apply Subtype.ext
    show a.1 * b.1 = b.1 * a.1
    rw [ha, hb]
    have h1 : e * e' = e' * e := comm_of_mem hE he he'
    have h2 : f * f' = f' * f := comm_of_mem hF hf hf'
    have h3 : f * e' = e' * f := (hEF e' he' f hf).symm
    have h4 : f' * e = e * f' := (hEF e he f' hf').symm
    calc e * f * (e' * f') = e * (f * e') * f' := by group
      _ = e * (e' * f) * f' := by rw [h3]
      _ = (e * e') * (f * f') := by group
      _ = (e' * e) * (f' * f) := by rw [h1, h2]
      _ = e' * (e * f') * f := by group
      _ = e' * (f' * e) * f := by rw [h4]
      _ = e' * f' * (e * f) := by group
  · obtain ⟨e, he, f, hf, rfl⟩ := hmem x hx
    have hc : Commute e f := hEF e he f hf
    rw [hc.mul_pow, hE.2 e he, hF.2 f hf, one_mul]

theorem card_eq_pow_of_elemAbelian [Finite G] {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) : ∃ k : ℕ, Nat.card E = p ^ k :=
  (IsPGroup.iff_card (p := p) (G := ↥E)).1 (isPGroup_of_elemAbelian hE)

theorem card_le_pow_pRank [Finite G] {p : ℕ} [hp : Fact p.Prime] {K E : Subgroup G} (hEK : E ≤ K)
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ CFSG.Open.pRank p K := by
  obtain ⟨k, hk⟩ := card_eq_pow_of_elemAbelian hE
  rw [hk]
  exact Nat.pow_le_pow_right hp.out.pos (CFSG.SectionRank.le_pRank hp.out.one_lt hEK hE hk)


theorem exists_elemAbelian_sq [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : IsPGroup p E) (hnc : ¬ IsCyclic E) :
    ∃ F : Subgroup G, F ≤ E ∧ IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
  haveI : Fact (IsPGroup p E) := ⟨hE⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  haveI := hSel
  have hSm : CFSG.IsElementaryAbelian p (S.map E.subtype) := CFSG.IsElementaryAbelian.map_subtype
  refine ⟨S.map E.subtype, Subgroup.map_subtype_le S,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hSm, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hScard]

theorem card_le_of_sylow [Finite G] {p : ℕ} [Fact p.Prime] {R : Subgroup G} (hR : IsSylowIn p ⊤ R)
    {k : ℕ} (hk : ∀ E : Subgroup G, E ≤ R → IsElemAbelian p E → Nat.card E ≤ p ^ k)
    {E : Subgroup G} (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ k := by
  let S : Sylow p G := ⟨R, hR.2.1, fun {Q} hQ hle => hR.2.2 Q le_top hQ hle⟩
  obtain ⟨Q, hQ⟩ := (isPGroup_of_elemAbelian hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hQR : ∀ x ∈ E, g⁻¹ * x * g ∈ R := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup G) := hQ hx
    rw [← hg, Sylow.coe_subgroup_smul] at hxQ
    obtain ⟨s, hs, hsx⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) (S : Subgroup G)).1 hxQ
    have : g⁻¹ * x * g = s := by
      rw [← hsx]
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hs
  have hE' : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    have := hQR x hx
    simpa [MulAut.conj_apply] using this
  have hE'el := CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj g⁻¹).toMonoidHom
  have := hk _ hE' hE'el
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at this


theorem card_gLBConj' (g : G) (H : Subgroup G) : Nat.card (GLBConj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem sylow_fusion [Finite G] {p : ℕ} [Fact p.Prime] {R : Subgroup G} (hR : IsSylowIn p ⊤ R)
    {x g : G} (hx : x ∈ centerOf R) (hgx : g * x * g⁻¹ ∈ centerOf R) :
    ∃ n ∈ Subgroup.normalizer (R : Set G), n * x * n⁻¹ = g * x * g⁻¹ := by
  set y := g * x * g⁻¹ with hy
  have hRx : R ≤ Subgroup.centralizer ({x} : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Lemma1315.mem_centerOf_iff'.1 hx).2 r hr
  have hRy : R ≤ Subgroup.centralizer ({y} : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Lemma1315.mem_centerOf_iff'.1 hgx).2 r hr
  have hR'y : GLBConj g⁻¹ R ≤ Subgroup.centralizer ({y} : Set G) := by
    intro r hr
    rw [mem_gLBConj, inv_inv] at hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hRx hr)
    calc r * y = g * ((g⁻¹ * r * g) * x) * g⁻¹ := by simp only [hy]; group
      _ = g * (x * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
      _ = y * r := by simp only [hy]; group
  have hR'p : IsPGroup p ↥(GLBConj g⁻¹ R) := hR.2.1.of_equiv (conjEquiv g⁻¹ R)
  obtain ⟨c, hcC, S, hSp, -, hRS, hcS⟩ := exists_conj_le_pGroup' (p := p) hRy hR.2.1 hR'y hR'p
  have hSR : S = R := hR.2.2 S le_top hSp hRS
  rw [hSR] at hcS
  have hcR : GLBConj c (GLBConj g⁻¹ R) = R := by
    refine Subgroup.eq_of_le_of_card_ge hcS ?_
    rw [card_gLBConj', card_gLBConj']
  rw [gLBConj_gLBConj] at hcR
  have hn : g⁻¹ * c ∈ Subgroup.normalizer (R : Set G) := mem_normalizer_iff_gLBConj_eq.2 hcR
  refine ⟨(g⁻¹ * c)⁻¹, inv_mem hn, ?_⟩
  have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  calc (g⁻¹ * c)⁻¹ * x * (g⁻¹ * c)⁻¹⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
    _ = c⁻¹ * y * c := rfl
    _ = y := by rw [mul_assoc, ← hcy]; group


abbrev conjAction (B H : Subgroup G) (h : B ≤ Subgroup.normalizer (H : Set G)) :
    MulDistribMulAction B H where
  smul b x := ⟨b * x * (b : G)⁻¹,
    Subgroup.le_normalizer_iff.mp h b b.property x x.property⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : G) * x * (1 : G)⁻¹ = x
    simp
  mul_smul b₁ b₂ x := by
    apply Subtype.ext
    change ((b₁ : G) * b₂) * x * ((b₁ : G) * b₂)⁻¹ = b₁ * (b₂ * x * (b₂ : G)⁻¹) * (b₁ : G)⁻¹
    simp [mul_assoc]
  smul_one b := by
    apply Subtype.ext
    change (b : G) * 1 * (b : G)⁻¹ = 1
    simp
  smul_mul b x y := by
    apply Subtype.ext
    change (b : G) * (x * y) * (b : G)⁻¹ = (b * x * (b : G)⁻¹) * (b * y * (b : G)⁻¹)
    simp [mul_assoc]

open scoped Pointwise in
theorem exists_normalized_sylow [Finite G] {p : ℕ} [Fact p.Prime] {H B : Subgroup G}
    (hB : IsPGroup p B) (hBH : B ≤ Subgroup.normalizer (H : Set G)) :
    ∃ P : Subgroup G, P ≤ H ∧ IsPGroup p P ∧
      (∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → P ≤ Q → Q = P) ∧
      B ≤ Subgroup.normalizer (P : Set G) := by
  letI : MulDistribMulAction B H := conjAction B H hBH
  have hnd : ¬ p ∣ Nat.card (Sylow p ↥H) := by
    have h1 := card_sylow_modEq_one p ↥H
    intro hd
    have h2 := (Nat.modEq_zero_iff_dvd.2 hd)
    have h3 := h2.symm.trans h1
    have : p ∣ 1 := (Nat.modEq_zero_iff_dvd).1 h3.symm
    exact (Fact.out : p.Prime).not_dvd_one this
  obtain ⟨P, hPfix⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p ↥H) hnd
  have hfix : ∀ b : B, b • P = P := MulAction.mem_fixedPoints.1 hPfix
  refine ⟨(P : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact IsPGroup.of_equiv P.isPGroup'
      (Subgroup.equivMapOfInjective (P : Subgroup ↥H) H.subtype H.subtype_injective)
  · intro Q hQH hQp hPQ
    have hQp' : IsPGroup p ↥(Q.subgroupOf H) :=
      IsPGroup.of_equiv hQp (Subgroup.subgroupOfEquivOfLe hQH).symm
    have hPle : (P : Subgroup ↥H) ≤ Q.subgroupOf H := fun x hx =>
      Subgroup.mem_subgroupOf.2 (hPQ ⟨x, hx, rfl⟩)
    have hQeq : Q.subgroupOf H = (P : Subgroup ↥H) := P.is_maximal' hQp' hPle
    ext x
    constructor
    · intro hx
      have hxH : x ∈ H := hQH hx
      have : (⟨x, hxH⟩ : ↥H) ∈ Q.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
      rw [hQeq] at this
      exact ⟨⟨x, hxH⟩, this, rfl⟩
    · exact fun hx => hPQ hx
  · have key : ∀ b ∈ B, ∀ x ∈ (P : Subgroup ↥H).map H.subtype, b * x * b⁻¹ ∈ (P : Subgroup ↥H).map H.subtype := by
      intro b hb x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hbP : (⟨b, hb⟩ : B) • P = P := hfix ⟨b, hb⟩
      have hmem : (⟨b, hb⟩ : B) • y ∈ (⟨b, hb⟩ : B) • (P : Subgroup ↥H) :=
        Subgroup.smul_mem_pointwise_smul y _ _ hy
      have hP' : ((⟨b, hb⟩ : B) • (P : Subgroup ↥H)) = (P : Subgroup ↥H) := by
        have := congrArg (fun Q : Sylow p ↥H => (Q : Subgroup ↥H)) hbP
        exact this
      rw [hP'] at hmem
      exact ⟨_, hmem, rfl⟩
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key b hb x
    · intro hx
      have := key b⁻¹ (inv_mem hb) _ hx
      simpa [mul_assoc] using this

end Generic


section Transfer

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barCongr {X Y : Type*} [Group X] [Group Y] (p : ℕ) (e : X ≃* Y) :
    (X ⧸ GLAPPrimeCore p X) ≃* (Y ⧸ GLAPPrimeCore p Y) :=
  QuotientGroup.congr _ _ e (glaPPrimeCore_map_iso p e)

theorem glaPComponent_subgroupOf {p : ℕ} (hp : p.Prime) {A K Y : Subgroup G}
    (hAY : A ≤ Y) (hK : GLAPComponent p A K) :
    GLAPComponent p (A.subgroupOf Y) (K.subgroupOf Y) := by
  have hker : Nat.Coprime p (Nat.card ↥(A.subgroupOf Y ⊓ Y.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hK' : GLAPComponent p ((A.subgroupOf Y).map Y.subtype) K := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAY]
    exact hK
  obtain ⟨K₀, hK₀, hK₀map⟩ := exists_glaPComponent_map_eq hp Y.subtype hker hK'
  have hsub : (K₀.map Y.subtype).subgroupOf Y = K₀ :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective K₀
  rw [hK₀map] at hsub
  rw [hsub]
  exact hK₀

theorem glaPComponent_barX_inf_centralizer {p : ℕ} (hp : p.Prime) {M L K : Subgroup G} {d : G}
    (hdM : d ∈ M) (hLM : L ≤ M) (hdL : d ∈ Subgroup.normalizer (L : Set G))
    (hd : IsPGroup p (Subgroup.zpowers d))
    (hK : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) K) :
    GLAPComponent p (barX p M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
      (barX p M K) := by
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup G := L ⊓ Subgroup.centralizer ({d} : Set G) with hA
  have hAM : A ≤ M := inf_le_left.trans hLM
  set ψ : ↥M →* ↥M ⧸ GLAPPrimeCore p ↥M := QuotientGroup.mk' (GLAPPrimeCore p ↥M) with hψ
  have hker : Nat.Coprime p (Nat.card ↥((A.subgroupOf M) ⊓ ψ.ker)) := by
    rw [hψ, QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  have hmap : (A.subgroupOf M).map ψ = barX p M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    barX_inf_centralizer hp hdM hLM hdL hd
  have h1 := glaPComponent_map hp ψ hker (glaPComponent_subgroupOf hp hAM hK)
  rw [hmap] at h1
  exact h1

@[expose] noncomputable def barOfBarX {p : ℕ} (hp : p.Prime) {M K : Subgroup G} (hKM : K ≤ M) :
    (↥K ⧸ GLAPPrimeCore p ↥K) ≃*
      (↥(barX p M K) ⧸ GLAPPrimeCore p ↥(barX p M K)) := by
  have hker : Nat.Coprime p (Nat.card ↥((K.subgroupOf M) ⊓
      (QuotientGroup.mk' (GLAPPrimeCore p ↥M)).ker)) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (haveI : Fact p.Prime := ⟨hp⟩; CFSG.pPrimeCore_coprime_card)
  exact (barCongr p (Subgroup.subgroupOfEquivOfLe hKM)).symm.trans
    (lcEquiv hp (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) (K.subgroupOf M) hker)

end Transfer


section Config

variable {G : Type} [Group G] [Finite G]

structure Basic (m p : ℕ) (B M R : Subgroup G) (d z : G) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  m4 : 4 ≤ m
  bel : IsElemAbelian p B
  bcard : Nat.card B = p ^ m
  bsc : IsSCp p ⊤ B
  bR : B ≤ R
  rM : R ≤ M
  rsyl : IsSylowIn p ⊤ R
  rk : ∀ E : Subgroup G, IsElemAbelian p E → Nat.card E ≤ p ^ m
  zB : z ∈ B
  z1 : z ≠ 1
  zo : orderOf z = p
  zR : ∀ r ∈ R, r * z = z * r
  dR : d ∈ R
  d1 : d ≠ 1
  dord : orderOf d = p
  dz : d * z = z * d
  normB : ∀ E : Subgroup G, E ≤ B → 2 ≤ CFSG.Open.pRank p E → Subgroup.normalizer (E : Set G) ≤ M
  core : GLAPPrimeCoreOf p (Cg z) ≤ M

theorem basic_of_cex {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) (hUR : U ≤ centerOf R) {z : G}
    (hz : z ∈ U ∧ z ≠ 1) : Basic m p B M R d z := by
  have hp : p.Prime := h.standing.prime
  have hp5 : 5 ≤ p := by
    have h3 : 3 < p := h139a.1
    have hne : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hRsyl : IsSylowIn p ⊤ R := Lemma1315.sylow_of_central_rank_two h hU.1 hUR
  have hBR : B ≤ R := le_trans le_sup_right h.hR.2
  have hrk : ∀ E : Subgroup G, IsElemAbelian p E → Nat.card E ≤ p ^ m := by
    intro E hE
    refine card_le_of_sylow hRsyl (k := m) (fun E' hE'R hE'el => ?_) hE
    have h1 : Nat.card E' ≤ p ^ CFSG.Open.pRank p M :=
      card_le_pow_pRank (hE'R.trans h.hR.1.1) hE'el
    have h2 : CFSG.Open.pRank p M ≤ m :=
      (pRank_le_glaTwoLocalRank hp.one_lt h.pre.1.1).trans h.standing.rank_eq.le
    exact h1.trans (Nat.pow_le_pow_right hp.pos h2)
  have hzB : z ∈ B := hU.1.1 hz.1
  have hzp : z ^ p = 1 := hU.1.2.1.2 z hz.1
  have hdA : d ∈ A := h.hD.1 h.hd.1
  have hdp : d ^ p = 1 := h.hD.2.1.2 d h.hd.1
  refine ⟨hp, hp5, h.standing.four_le, h.bOne.1.1, h.standing.card_eq h.bOne,
    lemma23_proved G m p h.standing B h.bOne, hBR, h.hR.1.1, hRsyl, hrk, hzB, hz.2,
    orderOf_eq_prime hzp hz.2, (Lemma1315.mem_centerOf_iff'.1 (hUR hz.1)).2,
    (le_trans le_sup_left h.hR.2) hdA, h.hd.2, orderOf_eq_prime hdp h.hd.2,
    (Subgroup.mem_centralizer_singleton_iff.1 (hU.2.1 hz.1)).symm, ?_, ?_⟩
  · intro E hEB hE2
    have hmemS : Subgroup.normalizer (E : Set G) ∈
        {N : Subgroup G | ∃ Q : Subgroup G, Q ≤ B ∧ 2 ≤ CFSG.Open.pRank p Q ∧
          N = Subgroup.normalizer (Q : Set G)} := ⟨E, hEB, hE2, rfl⟩
    exact le_trans (le_sSup hmemS) h.uniq.clause_d
  · have := h.uniq.clause_a z hzB hz.2
    exact le_trans le_sup_left this


theorem catalogIs_of_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs S' Q) : catalogIs S Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans f⟩⟩

theorem isChevSimple_of_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {r : ℕ}
    (h : IsChevSimple r S') : IsChevSimple r S := by
  rcases h with h | h
  · exact Or.inl (catalogIs_of_equiv e h)
  · exact Or.inr (catalogIs_of_equiv e h)

@[expose] noncomputable def centerQuotEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem isAltType_center_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : IsAltType n (B ⧸ Subgroup.center B)) : IsAltType n (A ⧸ Subgroup.center A) :=
  Lemma1314.isAltType_of_equiv (centerQuotEquiv e) h

theorem isChevSimple_center_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {r : ℕ}
    (h : IsChevSimple r (B ⧸ Subgroup.center B)) : IsChevSimple r (A ⧸ Subgroup.center A) :=
  isChevSimple_of_equiv (centerQuotEquiv e) h

theorem center_eq_bot_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd ((Subgroup.mem_center_iff.1 (by rw [h]; exact Subgroup.mem_top a) b).symm) hab

theorem centralizer_ne_top_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) {z : Q} (hz : z ≠ 1) :
    Subgroup.centralizer ({z} : Set Q) ≠ ⊤ := by
  intro htop
  have hzc : z ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({z} : Set Q) := by rw [htop]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  rw [center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hzc
  exact hz hzc


theorem Basic.R_le_Cg {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z) :
    R ≤ Cg z := fun r hr =>
  Subgroup.mem_centralizer_singleton_iff.2 (hb.zR r hr)

theorem Basic.B_le_Cg {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z) :
    B ≤ Cg z := hb.bR.trans hb.R_le_Cg

theorem Basic.d_mem_Cg {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z) :
    d ∈ Cg z := hb.R_le_Cg hb.dR

theorem Basic.pRank_B {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z) :
    CFSG.Open.pRank p B = m := by
  haveI : Fact p.Prime := ⟨hb.prime⟩
  exact le_antisymm (CFSG.SectionRank.pRank_le hb.prime.one_lt fun E _ hE => hb.rk E hE)
    (CFSG.SectionRank.le_pRank hb.prime.one_lt le_rfl hb.bel hb.bcard)

theorem card_le_barX {p : ℕ} [Fact p.Prime] {X : Subgroup G} {k : ℕ}
    (hk : ∀ E : Subgroup G, IsElemAbelian p E → Nat.card E ≤ p ^ k)
    {Eb : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} (hE : IsElemAbelian p Eb) :
    Nat.card Eb ≤ p ^ k := by
  haveI : (GLAPPrimeCore p ↥X).Normal := inferInstance
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).1 CFSG.pPrimeCore_coprime_card
  obtain ⟨S, hS, -, hScard⟩ := exists_elemAbelian_lift (GLAPPrimeCore p ↥X) hN hE
  have := hk (S.map X.subtype) (CFSG.SectionRank.isElemAbelian_map hS _)
  rwa [Subgroup.card_map_of_injective X.subtype_injective, hScard] at this

theorem le_M_of_type {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z)
    (hI : Input23_19) (hKP : CFSG.Open.IsKProper G) (hX : Cg z ≠ ⊤)
    {W : Subgroup G} (hW : GLAPComponent p (Cg z) W)
    (htype : (∃ n : ℕ, IsAltType n (barOf p W ⧸ Subgroup.center (barOf p W))) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (barOf p W ⧸ Subgroup.center (barOf p W)))) :
    W ≤ M := by
  have hp := hb.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hKX : CFSG.Open.IsKGroup ↥(Cg z) := CFSG.Open.IsKProper.isKGroup hKP (Cg z) hX
  haveI : (GLAPPrimeCore p ↥(Cg z)).Normal := inferInstance
  have hKY : CFSG.Open.IsKGroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) :=
    CFSG.Open.IsKGroup.quotient hKX _
  have hBp : IsPGroup p B := isPGroup_of_elemAbelian hb.bel
  have hrankB : CFSG.Open.pRank p (barX p (Cg z) B) = m := by
    rw [rank_barX_of_isPGroup hp hBp hb.B_le_Cg, hb.pRank_B]
  have htop : CFSG.Open.pRank p (⊤ : Subgroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))) ≤ m :=
    CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => card_le_barX hb.rk hE
  have hrk : CFSG.Open.pRank p (barX p (Cg z) B) =
      CFSG.Open.pRank p (⊤ : Subgroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))) :=
    le_antisymm (CFSG.SectionRank.pRank_mono hp.one_lt le_top) (hrankB ▸ htop)
  have hcomp := Lemma1314.isComponentOf_barX_of_glaPComponent hW
  have e := (quotEquivBarX hp hW.1 hW.2.1).symm
  have htype' : (∃ n : ℕ, IsAltType n (↥(barX p (Cg z) W) ⧸ Subgroup.center ↥(barX p (Cg z) W))) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧
        IsChevSimple q (↥(barX p (Cg z) W) ⧸ Subgroup.center ↥(barX p (Cg z) W))) := by
    rcases htype with ⟨n, hn⟩ | ⟨q, hq, hqp, hch⟩
    · exact Or.inl ⟨n, isAltType_center_of_equiv e hn⟩
    · exact Or.inr ⟨q, hq, hqp, isChevSimple_center_of_equiv e hch⟩
  have h23 := hI _ hKY p hp (by have := hb.five_le; omega) (barX p (Cg z) B)
    (isElemAbelian_barX hb.bel) (by rw [hrankB]; exact hb.m4) hrk _ hcomp (htype'.imp_right Or.inl)
  exact le_of_barX_le_glbCore hp 2 hBp hb.B_le_Cg hW.1 hb.normB hb.core h23


theorem coe_normalizerMonoidHom {L : Subgroup G} (γ : ↥(Subgroup.normalizer (L : Set G))) (x : ↥L) :
    ((L.normalizerMonoidHom γ x : ↥L) : G) = (γ : G) * x * (γ : G)⁻¹ := rfl

theorem mem_primeCoreOf_of_barAut_eq_one {p : ℕ} {L : Subgroup G}
    (c : ↥(Subgroup.normalizer (L : Set G))) (hc : barAut p L c = 1) {x : G} (hx : x ∈ L) :
    x⁻¹ * ((c : G) * x * (c : G)⁻¹) ∈ GLAPPrimeCoreOf p L := by
  have h := congrArg (fun f : MulAut (↥L ⧸ GLAPPrimeCore p ↥L) => f (QuotientGroup.mk ⟨x, hx⟩)) hc
  simp only [MulAut.one_apply] at h
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at h
  have h2 := QuotientGroup.eq.1 h.symm
  exact ⟨_, h2, by simp [coe_normalizerMonoidHom]⟩

theorem barX_comm_of_barAut_eq_one {p : ℕ} (hp : p.Prime) {X W : Subgroup G}
    (hWX : IsSubnormal W X) {e : G} (heX : e ∈ X) (heN : e ∈ Subgroup.normalizer (W : Set G))
    (he1 : barAut p W ⟨e, heN⟩ = 1) :
    ∀ w ∈ barX p X W, QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨e, heX⟩ * w =
      w * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨e, heX⟩ := by
  intro w hw
  obtain ⟨⟨w', hw'X⟩, hw'W, rfl⟩ := hw
  have hw'W' : w' ∈ W := Subgroup.mem_subgroupOf.1 hw'W
  have h1 := mem_primeCoreOf_of_barAut_eq_one (p := p) ⟨e, heN⟩ he1 hw'W'
  have h2 : (w'⁻¹ * (e * w' * e⁻¹) : G) ∈ GLAPPrimeCoreOf p X :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hWX h1
  obtain ⟨y, hy, hyx⟩ := h2
  set z : ↥X := (⟨w', hw'X⟩ : ↥X)⁻¹ * (⟨e, heX⟩ * ⟨w', hw'X⟩ * (⟨e, heX⟩ : ↥X)⁻¹) with hz
  have hyz : y = z := Subtype.ext hyx
  have h3 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) z = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hyz]
    exact hy
  rw [hz, map_mul, map_inv, map_mul, map_mul, map_inv] at h3
  have h5 := inv_mul_eq_one.1 h3
  exact (mul_inv_eq_iff_eq_mul.1 h5.symm)


theorem Basic.B_le_normalizer {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z)
    (hstd : GLStanding G m p) (hI : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    {W : Subgroup G} (hW : GLAPComponent p (Cg z) W) : B ≤ Subgroup.normalizer (W : Set G) := by
  by_contra hn
  have hrk : GLATwoLocalRank p ↥(Cg z) ≤ CFSG.Open.pRank p B :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hb.prime (Cg z)).trans
      (hstd.rank_eq.le.trans hb.pRank_B.symm.le)
  have h3 := (hI G m p hstd (Cg z) B W hb.bel hb.B_le_Cg hrk hW hn).1
  have := hb.five_le
  omega

theorem barAut_central_eq_one {p : ℕ} {W : Subgroup G} {z : G} (hW : W ≤ Cg z)
    (hzN : z ∈ Subgroup.normalizer (W : Set G)) :
    barAut p W ⟨z, hzN⟩ = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    have hc : z * (x : G) = (x : G) * z :=
      (Subgroup.mem_centralizer_singleton_iff.1 (hW x.2)).symm
    show z * (x : G) * z⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact hc

theorem Basic.centBar_B_eq {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z)
    (hstd : GLStanding G m p) (hI : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    {W : Subgroup G} (hW : GLAPComponent p (Cg z) W) (hWM : ¬ W ≤ M) :
    centBar p B W = Subgroup.zpowers z := by
  have hp := hb.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hBN := hb.B_le_normalizer hstd hI hW
  have hBp : IsPGroup p B := isPGroup_of_elemAbelian hb.bel
  set E := centBar p B W with hE
  have hEB : E ≤ B := inf_le_right
  have hEel : IsElemAbelian p E := elemAbelian_mono hb.bel hEB
  have hzN : z ∈ Subgroup.normalizer (W : Set G) := by
    refine Subgroup.centralizer_le_normalizer (W : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hW.1 hy)
  have hzE : z ∈ E := ⟨⟨⟨z, hzN⟩, barAut_central_eq_one hW.1 hzN, rfl⟩, hb.zB⟩
  have hrank1 : CFSG.Open.pRank p E ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ CFSG.Open.pRank p E := by omega
    have hEC : E ≤ Cg z := hEB.trans hb.B_le_Cg
    have hEp : IsPGroup p E := isPGroup_of_elemAbelian hEel
    have hrE : CFSG.Open.pRank p (barX p (Cg z) E) = CFSG.Open.pRank p E :=
      rank_barX_of_isPGroup hp hEp hEC
    have hEhat : barX p (Cg z) E ≤ barX p (Cg z) B := Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.2 (hEB (Subgroup.mem_subgroupOf.1 hx))
    have hN : Subgroup.normalizer ((barX p (Cg z) E : Subgroup _) : Set _) ≤
        GLBCore p 2 (barX p (Cg z) B) :=
      le_sSup ⟨barX p (Cg z) E, hEhat, by rw [hrE]; exact h2, rfl⟩
    have hWhat : barX p (Cg z) W ≤ GLBCore p 2 (barX p (Cg z) B) := by
      intro w hw
      have hwc : w ∈ Subgroup.centralizer ((barX p (Cg z) E : Subgroup _) : Set _) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨⟨e, heX⟩, heE, rfl⟩
        have heE' : e ∈ E := Subgroup.mem_subgroupOf.1 heE
        obtain ⟨⟨n, hn1, hne⟩, -⟩ := heE'
        have hneN : e ∈ Subgroup.normalizer (W : Set G) := hne ▸ n.2
        have h1 : barAut p W ⟨e, hneN⟩ = 1 := by
          have : (⟨e, hneN⟩ : ↥(Subgroup.normalizer (W : Set G))) = n := Subtype.ext hne.symm
          rw [this]; exact hn1
        exact barX_comm_of_barAut_eq_one hp hW.2.1 heX hneN h1 w hw
      exact hN (Subgroup.centralizer_le_normalizer _ hwc)
    exact hWM (le_of_barX_le_glbCore hp 2 hBp hb.B_le_Cg hW.1 hb.normB hb.core hWhat)
  have hcardE : Nat.card E ≤ p := by
    obtain ⟨k, hk⟩ := card_eq_pow_of_elemAbelian hEel
    have hk1 : k ≤ 1 := (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEel hk).trans hrank1
    rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, hb.zo]
  have hle : Subgroup.zpowers z ≤ E := (Subgroup.zpowers_le).2 hzE
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hzcard]; exact hcardE)).symm


theorem isChevSimple_two_of_isChevTwo {S : Type} [Group S]
    (h : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo S) : IsChevSimple 2 S := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · refine Or.inl ⟨.lie d, ?_, ⟨e⟩⟩
    obtain ⟨d, hdv⟩ := d
    cases d <;> simp_all [CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo,
      CFSG.Yardstones.Md0ec50421ce4.onLie]
  · have h5 : 5 ≤ n := by rcases hn with rfl | rfl | rfl <;> norm_num
    refine Or.inr ⟨.alternating n h5, ?_, ⟨e⟩⟩
    rcases hn with rfl | rfl | rfl <;> simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev]
  · refine Or.inr ⟨.lie d, ?_, ⟨e⟩⟩
    obtain ⟨d, hdv⟩ := d
    rcases hd with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have hq' : q.p ^ q.exponent = 7 := (TauCeti.PrimePower.card_def q).symm.trans hq
      simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev, hq']
    · have hq' : q.p ^ q.exponent = 3 := (TauCeti.PrimePower.card_def q).symm.trans hq
      simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev, hq']

theorem catalog_cases {S : Type} [Group S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (hcat : CFSG.Open.IsCatalogGroup S) :
    (∃ n : ℕ, IsAltType n S) ∨
      (∃ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) ∨
      (∃ name : TauCeti.SporadicName, IsSporType name S) := by
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h1 : e (a * b) = e (b * a) := by
      rw [map_mul, map_mul]
      exact mul_comm _ _
    exact e.injective h1
  | alternating n hn => exact Or.inl ⟨n, ⟨e⟩⟩
  | lie idx => exact Or.inr (Or.inl ⟨idx, ⟨e⟩⟩)
  | sporadic name => exact Or.inr (Or.inr ⟨name, ⟨e⟩⟩)

theorem isAltType_center_quot {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n) (h : IsAltType n X) :
    IsAltType n (X ⧸ Subgroup.center X) := by
  obtain ⟨e⟩ := h
  have hc : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  have e1 := centerQuotEquiv e
  have e2 : (alternatingGroup (Fin n) ⧸ Subgroup.center (alternatingGroup (Fin n))) ≃*
      alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact ⟨e1.trans e2⟩

end Config


section YLevel

variable {G : Type} [Group G] [Finite G]

theorem primeCoreOf_top_eq_bot {p : ℕ} {Y : Type} [Group Y] [Finite Y]
    (hY : GLAPPrimeCore p Y = ⊥) : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
  have hiso := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y)
  rw [hY] at hiso
  have h1 : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hm : (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y) x ∈
        (GLAPPrimeCore p ↥(⊤ : Subgroup Y)).map
          (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hiso, Subgroup.mem_bot] at hm
    rw [Subgroup.mem_bot]
    exact (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).injective (hm.trans (map_one _).symm)
  unfold GLAPPrimeCoreOf
  rw [h1, Subgroup.map_bot]

theorem primeCore_sub_eq_bot {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (hY : GLAPPrimeCore p Y = ⊥) {S : Subgroup Y} (hS : IsSubnormal S ⊤) :
    GLAPPrimeCore p ↥S = ⊥ := by
  have h1 : GLAPPrimeCoreOf p S ≤ GLAPPrimeCoreOf p (⊤ : Subgroup Y) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hS
  rw [primeCoreOf_top_eq_bot hY] at h1
  rw [eq_bot_iff]
  intro x hx
  have hm : (x : Y) ∈ GLAPPrimeCoreOf p S := Subgroup.mem_map_of_mem S.subtype hx
  have := h1 hm
  rw [Subgroup.mem_bot] at this ⊢
  exact Subtype.ext this

theorem core_barX_eq_bot {p : ℕ} (hp : p.Prime) {C H : Subgroup G} (hH : GLAPComponent p C H) :
    GLAPPrimeCore p ↥(barX p C H) = ⊥ :=
  primeCore_sub_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp)
    (Lemma1314.isComponentOf_barX_of_glaPComponent hH).2.1

theorem isKHat_barX {p : ℕ} (hp : p.Prime) {C H : Subgroup G} (hC : CFSG.Open.IsKGroup ↥C)
    (hH : GLAPComponent p C H) : IsKHat ↥(barX p C H) := by
  haveI : (GLAPPrimeCore p ↥C).Normal := inferInstance
  have hY : CFSG.Open.IsKGroup (↥C ⧸ GLAPPrimeCore p ↥C) := CFSG.Open.IsKGroup.quotient hC _
  have hcomp := Lemma1314.isComponentOf_barX_of_glaPComponent hH
  refine ⟨hcomp.2.2, ?_⟩
  haveI : IsSimpleGroup (↥(barX p C H) ⧸ Subgroup.center ↥(barX p C H)) := hcomp.2.2.2
  have hperf : commutator ↥(barX p C H) = ⊤ := hcomp.2.2.1
  have hnt : Nontrivial (↥(barX p C H) ⧸ Subgroup.center ↥(barX p C H)) := inferInstance
  have hnab : ∃ a b : ↥(barX p C H) ⧸ Subgroup.center ↥(barX p C H), a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have hle : commutator ↥(barX p C H) ≤ Subgroup.center ↥(barX p C H) := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g _ h _
      rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
        hcomm (g : ↥(barX p C H) ⧸ Subgroup.center ↥(barX p C H)) h]
      group
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥(barX p C H) ⧸ Subgroup.center ↥(barX p C H))
    induction q using QuotientGroup.induction_on with
    | H g =>
      exact hq ((QuotientGroup.eq_one_iff g).mpr (hle (by rw [hperf]; exact Subgroup.mem_top g)))
  exact CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hY (barX p C H) hnab
    (QuotientGroup.mk' (Subgroup.center ↥(barX p C H))) (QuotientGroup.mk'_surjective _)


noncomputable abbrev conjAutOf {Y : Type} [Group Y] (K : Subgroup Y) (d : Y)
    (hd : d ∈ Subgroup.normalizer (K : Set Y)) : MulAut ↥K :=
  K.normalizerMonoidHom ⟨d, hd⟩

theorem coe_conjAutOf {Y : Type} [Group Y] (K : Subgroup Y) (d : Y)
    (hd : d ∈ Subgroup.normalizer (K : Set Y)) (k : ↥K) :
    ((conjAutOf K d hd k : ↥K) : Y) = d * k * d⁻¹ := rfl

theorem pumpupVia_of_setting {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {K J : Subgroup Y} {d : Y} (hdK : d ∈ Subgroup.normalizer (K : Set Y)) (hd : d ^ p = 1)
    (hnt : ¬ K ≤ Subgroup.centralizer ({d} : Set Y))
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set Y)) J) :
    Lemma1314.PumpupVia p (barOf p J) ↥K (conjAutOf K d hdK) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hpow : (conjAutOf K d hdK) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨d, hdK⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ p = 1 := Subtype.ext hd
    rw [this, map_one]
  have hne : conjAutOf K d hdK ≠ 1 := by
    intro h1
    apply hnt
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : Y)) h1
    simp only [MulAut.one_apply] at this
    rw [coe_conjAutOf] at this
    have h2 : d * k * d⁻¹ = k := this
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  refine ⟨orderOf_eq_prime hpow hne, J.subgroupOf K, ?_, ⟨barCongr p (Subgroup.subgroupOfEquivOfLe hJK)⟩⟩
  have hfix : Lemma1314.fixSub (conjAutOf K d hdK) =
      (K ⊓ Subgroup.centralizer ({d} : Set Y)).subgroupOf K := by
    ext k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      have hk' : conjAutOf K d hdK k = k := hk
      have h2 := congrArg (fun x : ↥K => (x : Y)) hk'
      simp only [coe_conjAutOf] at h2
      refine ⟨k.2, ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · rintro ⟨-, hk⟩
      show conjAutOf K d hdK k = k
      apply Subtype.ext
      rw [coe_conjAutOf, mul_inv_eq_iff_eq_mul]
      exact hk.symm
  rw [hfix]
  exact glaPComponent_subgroupOf hp (inf_le_left : K ⊓ Subgroup.centralizer ({d} : Set Y) ≤ K) hJ

theorem mem_innerAut_of_innerOn {Y : Type} [Group Y] {K : Subgroup Y} {d : Y}
    (hd : d ∈ Subgroup.normalizer (K : Set Y)) {k : Y} (hk : k ∈ K)
    (h : ∀ y ∈ K, d * y * d⁻¹ = k * y * k⁻¹) : conjAutOf K d hd ∈ innerAut ↥K := by
  refine ⟨⟨k, hk⟩, ?_⟩
  ext y
  show ((MulAut.conj (⟨k, hk⟩ : ↥K) y : ↥K) : Y) = ((conjAutOf K d hd y : ↥K) : Y)
  rw [coe_conjAutOf, MulAut.conj_apply]
  exact (h y y.2).symm


theorem innerOn_of_inducesInner {p : ℕ} (hp : p.Prime) {X H : Subgroup G} (hHX : IsSubnormal H X)
    {d : G} (hdX : d ∈ X) (hI : InducesInner p H d) :
    ∃ k ∈ barX p X H, ∀ y ∈ barX p X H,
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d, hdX⟩ * y *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d, hdX⟩)⁻¹ =
        k * y * k⁻¹ := by
  obtain ⟨k, hkH, hc⟩ := hI
  have hHXle : H ≤ X := hHX.le
  have hkX : k ∈ X := hHXle hkH
  obtain ⟨⟨n, hn1, hne⟩, -⟩ := hc
  refine ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨k, hkX⟩,
    ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.2 hkH, rfl⟩, ?_⟩
  rintro _ ⟨⟨y, hyX⟩, hyH, rfl⟩
  have hyH' : y ∈ H := Subgroup.mem_subgroupOf.1 hyH
  have h1 := mem_primeCoreOf_of_barAut_eq_one (p := p) n hn1 hyH'
  have hne' : (n : G) = k⁻¹ * d := hne
  rw [hne'] at h1
  have h2 : y⁻¹ * ((k⁻¹ * d) * y * (k⁻¹ * d)⁻¹) ∈ GLAPPrimeCoreOf p X :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hHX h1
  obtain ⟨u, hu, hux⟩ := h2
  set kx : ↥X := ⟨k, hkX⟩
  set dx : ↥X := ⟨d, hdX⟩
  set yx : ↥X := ⟨y, hyX⟩
  have hu' : u = yx⁻¹ * ((kx⁻¹ * dx) * yx * (kx⁻¹ * dx)⁻¹) := Subtype.ext hux
  have hnorm : kx * u * kx⁻¹ ∈ GLAPPrimeCore p ↥X :=
    (GLAPPrimeCore.normal p ↥X).conj_mem u hu kx
  have heq : kx * u * kx⁻¹ = (kx * yx * kx⁻¹)⁻¹ * (dx * yx * dx⁻¹) := by
    rw [hu']
    group
  rw [heq] at hnorm
  have h3 : (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) (dx * yx * dx⁻¹) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) (kx * yx * kx⁻¹) :=
    (QuotientGroup.eq.2 hnorm).symm
  simpa only [map_mul, map_inv] using h3


theorem isLpType_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n Q : ℕ}
    (h : IsLpType n Q Y) : IsLpType n Q X := by
  obtain ⟨F, hF, hFin, hcard, ⟨f⟩⟩ := h
  exact ⟨F, hF, hFin, hcard, ⟨e.trans f⟩⟩

theorem isQuasisimple_barOf_of_comp {p : ℕ} (hp : p.Prime) {C L : Subgroup G}
    (h : GLAPComponent p C L) : CFSG.Open.IsQuasisimple (barOf p L) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (quotEquivBarX hp h.1 h.2.1).symm h.2.2.1.2.2

theorem card_barX_eq {p : ℕ} (hp : p.Prime) {C E : Subgroup G} (hE : IsPGroup p E) (hEC : E ≤ C) :
    Nat.card (barX p C E) = Nat.card E := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (E.subgroupOf C).subtype with hf
  have hfi := injective_barX_comp hp hE hEC
  have hrange : f.range = barX p C E := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv]

theorem conj_mem_barX {p : ℕ} {X H : Subgroup G} {d : G} (hdX : d ∈ X)
    (hdH : d ∈ Subgroup.normalizer (H : Set G))
    {k : ↥X ⧸ GLAPPrimeCore p ↥X} (hk : k ∈ barX p X H) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d, hdX⟩ * k *
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d, hdX⟩)⁻¹ ∈ barX p X H := by
  obtain ⟨⟨h, hhX⟩, hhH, rfl⟩ := hk
  have hhH' : h ∈ H := Subgroup.mem_subgroupOf.1 hhH
  have hdhH : d * h * d⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hdH h).1 hhH'
  have hmem : d * h * d⁻¹ ∈ X := X.mul_mem (X.mul_mem hdX hhX) (X.inv_mem hdX)
  have hxe : (⟨d * h * d⁻¹, hmem⟩ : ↥X) = ⟨d, hdX⟩ * ⟨h, hhX⟩ * (⟨d, hdX⟩ : ↥X)⁻¹ := rfl
  refine ⟨⟨d * h * d⁻¹, hmem⟩, Subgroup.mem_subgroupOf.2 hdhH, ?_⟩
  rw [hxe]
  simp only [map_mul, map_inv]

theorem mk_mem_normalizer_barX {p : ℕ} {X H : Subgroup G} {d : G} (hdX : d ∈ X)
    (hdH : d ∈ Subgroup.normalizer (H : Set G)) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d, hdX⟩ ∈
      Subgroup.normalizer ((barX p X H : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact conj_mem_barX hdX hdH hk
  · intro hk
    have h1 := conj_mem_barX (p := p) (X := X) (H := H) (X.inv_mem hdX)
      ((Subgroup.normalizer (H : Set G)).inv_mem hdH) hk
    have : (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) ⟨d⁻¹, X.inv_mem hdX⟩ =
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥X)) ⟨d, hdX⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this, inv_inv] at h1
    simpa [mul_assoc] using h1

theorem eq_of_perfect_subnormal_quasisimple {Y : Type} [Group Y] {K J : Subgroup Y}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hJ1 : J ≠ ⊥) (hper : ⁅J, J⁆ = J)
    (hsn : IsSubnormal J K) : J = K := by
  have hJK : J ≤ K := hsn.le
  have hsn' : IsSubnormal (J.subgroupOf K) (⊤ : Subgroup ↥K) := by
    have h1 := hsn.comap K.subtype
    have h2 : K.comap K.subtype = ⊤ := Subgroup.subgroupOf_self K
    rwa [h2] at h1
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hK _ hsn' with
    hc | htop
  · exfalso
    apply hJ1
    have hab : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
      intro a ha b hb
      have : (⟨a, hJK ha⟩ : ↥K) ∈ Subgroup.center ↥K := hc (Subgroup.mem_subgroupOf.2 ha)
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 this ⟨b, hJK hb⟩).symm)
    have hle : ⁅J, J⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a ha b hb
    rw [hper] at hle
    exact le_bot_iff.1 hle
  · refine le_antisymm hJK fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ J.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this


theorem exists_noncomm_quot {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  have hperf : commutator K = ⊤ := hK.1
  by_contra hcomm
  push Not at hcomm
  have hle : commutator K ≤ Subgroup.center K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hcomm (g : K ⧸ Subgroup.center K) h]
    group
  obtain ⟨q, hq⟩ := exists_ne (1 : K ⧸ Subgroup.center K)
  induction q using QuotientGroup.induction_on with
  | H g =>
    exact hq ((QuotientGroup.eq_one_iff g).mpr (hle (by rw [hperf]; exact Subgroup.mem_top g)))

theorem isChevSimple_of_lie {S : Type} [Group S] {idx : TauCeti.ValidLieTypeIndex}
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) : IsChevSimple idx.1.characteristic S :=
  Or.inl ⟨.lie idx, rfl, ⟨e⟩⟩

theorem orderOf_mk_eq {p : ℕ} [Fact p.Prime] {X : Subgroup G} {d : G} (hdX : d ∈ X)
    (hd : orderOf d = p) :
    orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨d, hdX⟩) = p := by
  have hp : p.Prime := Fact.out
  have hdp : d ^ p = 1 := hd ▸ pow_orderOf_eq_one d
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨d, hdX⟩ : ↥X) ^ p = 1 := Subtype.ext hdp
    rw [this, map_one]
  · intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hdvd := Subgroup.orderOf_dvd_natCard (GLAPPrimeCore p ↥X) h1
    have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥X) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
    apply hN
    have h2 : orderOf (⟨d, hdX⟩ : ↥X) = p := by
      rw [← Subgroup.orderOf_coe]
      exact hd
    rwa [h2] at hdvd

theorem exists_B4 {p m : ℕ} [Fact p.Prime] {B : Subgroup G} (hB : IsElemAbelian p B)
    (hcard : Nat.card B = p ^ m) (hm : 4 ≤ m) :
    ∃ B4 : Subgroup G, B4 ≤ B ∧ IsElemAbelian p B4 ∧ Nat.card B4 = p ^ 4 := by
  have hdvd : p ^ 4 ∣ Nat.card B := hcard ▸ pow_dvd_pow p hm
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine ⟨K.map B.subtype, Subgroup.map_subtype_le K,
    elemAbelian_mono hB (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective B.subtype_injective, hK]


theorem exists_elemAbelian_lift_above {Z : Type*} [Group Z] [Finite Z] {p : ℕ} [hp : Fact p.Prime]
    (N : Subgroup Z) [N.Normal] (hN : ¬ p ∣ Nat.card N) {Eb : Subgroup (Z ⧸ N)}
    (hE : IsElemAbelian p Eb) {A : Subgroup Z} (hA : IsPGroup p A)
    (hAE : A.map (QuotientGroup.mk' N) ≤ Eb) :
    ∃ S : Subgroup Z, A ≤ S ∧ IsElemAbelian p S ∧ S.map (QuotientGroup.mk' N) = Eb := by
  have hcop : ∀ {k : ℕ}, Nat.Coprime (p ^ k) (Nat.card N) := fun {k} =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)
  have hEp : IsPGroup p Eb := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨k, hcard⟩ := hEp.exists_card_eq
  set P : Subgroup Z := Eb.comap (QuotientGroup.mk' N) with hP
  have hPcard : Nat.card P = Nat.card N * p ^ k := by
    rw [← hcard]
    exact QuotientGroup.card_preimage_mk N (Eb : Set (Z ⧸ N))
  have hAP : A ≤ P := fun a ha => hAE ⟨a, ha, rfl⟩
  have hA' : IsPGroup p ↥(A.subgroupOf P) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAP).symm
  obtain ⟨S, hAS⟩ := hA'.exists_le_sylow
  have hScard : Nat.card S = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow hp.out,
      Finsupp.single_eq_same, zero_add]
  set ι : S →* Z := P.subtype.comp (S : Subgroup P).subtype
  set φ : S →* Eb := ((QuotientGroup.mk' N).comp ι).codRestrict Eb fun s => s.1.2
  have hker : ∀ s : S, ι s ∈ N → s = 1 := by
    intro s hs
    have hdisj := Subgroup.disjoint_of_coprime_natCard (H := (S : Subgroup P).map P.subtype)
      (K := N) (by
        rw [Subgroup.card_map_of_injective Subtype.val_injective, hScard]
        exact hcop)
    have h1 : ι s ∈ (S : Subgroup P).map P.subtype ⊓ N := ⟨⟨s, s.2, rfl⟩, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h2 : (QuotientGroup.mk' N) (ι s) = 1 := congrArg Subtype.val hs
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact (Subgroup.mem_bot).2 (hker s h2)
  have hιinj : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have := hE.1
  have hsurj : Function.Surjective φ :=
    (hφ.bijective_of_nat_card_le (by rw [hcard, hScard])).2
  refine ⟨ι.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · intro a ha
    have haP : a ∈ P := hAP ha
    have hmem : (⟨a, haP⟩ : ↥P) ∈ (S : Subgroup P) := hAS (Subgroup.mem_subgroupOf.2 ha)
    exact ⟨⟨⟨a, haP⟩, hmem⟩, rfl⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : Z) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul]
    congr 1
    apply hφ
    rw [map_mul, map_mul]
    exact mul_comm' _ _
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have : x ^ p = 1 := by
      apply hφ
      rw [map_pow, map_one]
      exact Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE.2 _ (φ x).2)
    rw [this, map_one]
  · ext e
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact (φ s).2
    · intro he
      obtain ⟨s, hs⟩ := hsurj ⟨e, he⟩
      exact ⟨ι s, ⟨s, rfl⟩, congrArg Subtype.val hs⟩

theorem isSCp_barX {p : ℕ} (hp : p.Prime) {X A : Subgroup G} (hA : IsSCp p X A) :
    IsSCp p ⊤ (barX p X A) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (GLAPPrimeCore p ↥X).Normal := inferInstance
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  refine ⟨le_top, isElemAbelian_barX hA.2.1, fun E _ hE hAE => ?_⟩
  have hAX : A ≤ X := hA.1
  have hAp : IsPGroup p ↥(A.subgroupOf X) :=
    (isPGroup_of_elemAbelian hA.2.1).of_equiv (Subgroup.subgroupOfEquivOfLe hAX).symm
  have hAE' : (A.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) ≤ E := hAE
  obtain ⟨S, hAS, hSel, hSmap⟩ := exists_elemAbelian_lift_above (GLAPPrimeCore p ↥X) hN hE hAp hAE'
  have hSG : IsElemAbelian p (S.map X.subtype) := CFSG.SectionRank.isElemAbelian_map hSel _
  have hAle : A ≤ S.map X.subtype := by
    intro a ha
    exact ⟨⟨a, hAX ha⟩, hAS (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  have hSA : S.map X.subtype = A := hA.2.2 _ (Subgroup.map_subtype_le S |>.trans le_rfl) hSG hAle
  have hSeq : S = A.subgroupOf X := by
    rw [← hSA]
    exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective S).symm
  rw [← hSmap, hSeq]
  rfl

end YLevel


section TypeAnalysis

variable {G : Type} [Group G] [Finite G]

theorem mem_center_cg {z : G} : z ∈ Cg z := Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem le_M_of_spor {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z)
    (hI : Input25_5) (hKP : CFSG.Open.IsKProper G) (hX : Cg z ≠ ⊤)
    {H H0 : Subgroup G} (hHc : GLAPComponent p (Cg z) H)
    (hdH : d ∈ Subgroup.normalizer (H : Set G)) (hH0 : GLAPComponent p (H ⊓ Cg d) H0)
    (hch : IsChevSimple 2 (barOf p H0 ⧸ Subgroup.center (barOf p H0)))
    (hspor : ∃ name : TauCeti.SporadicName, IsSporType name
      (↥(barX p (Cg z) H) ⧸ Subgroup.center ↥(barX p (Cg z) H)))
    {A : Subgroup G} (hA : IsSCp p (Cg z) A) (hAr : CFSG.Open.pRank p A = 3) (hdA : d ∈ A)
    (hzA : z ∈ A) : H ≤ M := by
  have hp := hb.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hdX : d ∈ Cg z := hb.d_mem_Cg
  have hzX : z ∈ Cg z := mem_center_cg
  have hHX : H ≤ Cg z := hHc.1
  have hKX : CFSG.Open.IsKGroup ↥(Cg z) := CFSG.Open.IsKProper.isKGroup hKP (Cg z) hX
  haveI : (GLAPPrimeCore p ↥(Cg z)).Normal := inferInstance
  have hY : CFSG.Open.IsKGroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) :=
    CFSG.Open.IsKGroup.quotient hKX _
  have hcomp := Lemma1314.isComponentOf_barX_of_glaPComponent hHc
  have hdK := mk_mem_normalizer_barX (p := p) hdX hdH
  have hdord := orderOf_mk_eq (p := p) hdX hb.dord
  have hH0X : H0 ≤ Cg z := hH0.1.trans (inf_le_left.trans hHX)
  have hdz : IsPGroup p ↥(Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb.dord, pow_one])
  have hJ := glaPComponent_barX_inf_centralizer hp hdX hHX hdH hdz hH0
  have hbJ : ∃ J : Subgroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)),
      GLAPComponent p (barX p (Cg z) H ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩} : Set _)) J ∧
        IsChevSimple 2 (PSimple p J) :=
    ⟨barX p (Cg z) H0, hJ, isChevSimple_center_of_equiv (barOfBarX hp hH0X).symm hch⟩
  have hApG : IsPGroup p A := isPGroup_of_elemAbelian hA.2.1
  have hAX : A ≤ Cg z := hA.1
  have hzne : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨z, hzX⟩ ≠ 1 := by
    intro h1
    have := orderOf_mk_eq (p := p) hzX hb.zo
    rw [h1, orderOf_one] at this
    exact hp.ne_one this.symm
  have hzA' : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨z, hzX⟩ ∈ barX p (Cg z) A :=
    ⟨⟨z, hzX⟩, Subgroup.mem_subgroupOf.2 hzA, rfl⟩
  have hzcen : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨z, hzX⟩ ∈
      Subgroup.center (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      show (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z))) (x * ⟨z, hzX⟩) =
        (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z))) (⟨z, hzX⟩ * x)
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.1 x.2)
  have hc : ∃ A' : Subgroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)), IsSCp p ⊤ A' ∧
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩ ∈ A' ∧ CFSG.Open.pRank p A' = 3 ∧
      A' ⊓ Subgroup.center (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) ≠ ⊥ := by
    refine ⟨barX p (Cg z) A, isSCp_barX hp hA, ⟨⟨d, hdX⟩, Subgroup.mem_subgroupOf.2 hdA, rfl⟩,
      ?_, ?_⟩
    · rw [rank_barX_of_isPGroup hp hApG hAX, hAr]
    · intro hbot
      have : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨z, hzX⟩ ∈
          barX p (Cg z) A ⊓ Subgroup.center (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) := ⟨hzA', hzcen⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hzne this
  obtain ⟨B4, hB4B, hB4el, hB4card⟩ := exists_B4 hb.bel hb.bcard hb.m4
  have hB4p : IsPGroup p B4 := isPGroup_of_elemAbelian hB4el
  have hB4X : B4 ≤ Cg z := hB4B.trans hb.B_le_Cg
  have hE4 : IsEkIn p 4 ⊤ (barX p (Cg z) B4) :=
    ⟨le_top, isElemAbelian_barX hB4el, by rw [card_barX_eq hp hB4p hB4X, hB4card]⟩
  have hL := hI _ p hp hb.five_le hY (barX p (Cg z) H) (QuotientGroup.mk' _ ⟨d, hdX⟩) hcomp hdK hdord
    hspor hbJ hc _ hE4
  exact le_of_barX_le_glbCore hp 2 hB4p hB4X hHX
    (fun E hE hr => hb.normB E (hE.trans hB4B) hr) hb.core hL


structure Inputs : Prop where
  i2319 : Input23_19
  i255 : Input25_5
  i33 : Input3_3
  i144 : Input14_4_1
  i1418 : Input14_18
  i1415 : Lemma1314.Input14_15
  iFi23 : Lemma1314.Input23_24Fi23
  i112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2
  i183 : Prop115.Input18_3Gen
  iDiag : Input18_3DiagZ
  iL2 : InputL2

theorem cg2_le_cg_d {d z : G} : Cg2 d z ≤ Cg d :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert d {z}))

theorem inf_le_cg2 {d z : G} {H : Subgroup G} (hH : H ≤ Cg z) : H ⊓ Cg d ≤ Cg2 d z := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hy with rfl | hy
  · exact (Subgroup.mem_centralizer_singleton_iff.1 hx.2).symm
  · rw [Set.mem_singleton_iff.1 hy]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hH hx.1)).symm

theorem ne_bot_of_quasisimple_quot {Y : Type} [Group Y] {J : Subgroup Y} {N : Subgroup ↥J}
    [N.Normal] (h : CFSG.Open.IsQuasisimple (↥J ⧸ N)) : J ≠ ⊥ := by
  haveI : IsSimpleGroup ((↥J ⧸ N) ⧸ Subgroup.center (↥J ⧸ N)) := h.2
  haveI : Nontrivial (↥J ⧸ N) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (↥J ⧸ N))).nontrivial
  haveI : Nontrivial ↥J := (QuotientGroup.mk_surjective (s := N)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot J).1 this

@[expose] noncomputable def iso_of_eq_of_core {p : ℕ} {Y : Type} [Group Y] {J K : Subgroup Y}
    (h : J = K) (hK : GLAPPrimeCore p ↥K = ⊥) : (↥J ⧸ GLAPPrimeCore p ↥J) ≃* ↥K := by
  subst h
  exact (QuotientGroup.quotientMulEquivOfEq hK).trans QuotientGroup.quotientBot

theorem single_case {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z)
    (hI : Inputs) (hstd : GLStanding G m p) (hX : Cg z ≠ ⊤)
    {H H0 : Subgroup G} (hHc : GLAPComponent p (Cg z) H)
    (hdH : d ∈ Subgroup.normalizer (H : Set G)) (hH0H : H0 ≤ H)
    (hH0 : GLAPComponent p (Cg2 d z) H0) (hHM : ¬ H ≤ M)
    (hH0t : Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0)))
    {A : Subgroup G} (hA : IsSCp p (Cg z) A) (hAr : CFSG.Open.pRank p A = 3) (hdA : d ∈ A)
    (hzA : z ∈ A) :
    (p = 5 ∨ p = 7) ∧ IsLpType 2 p (barOf p H0) ∧ IsLpType 2 (p ^ p) (barOf p H) ∧
      ¬ InducesInner p H d := by
  have hp := hb.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hKP : CFSG.Open.IsKProper G := hstd.kProper
  have hdX : d ∈ Cg z := hb.d_mem_Cg
  have hHX : H ≤ Cg z := hHc.1
  have hKX : CFSG.Open.IsKGroup ↥(Cg z) := CFSG.Open.IsKProper.isKGroup hKP (Cg z) hX
  haveI : (GLAPPrimeCore p ↥(Cg z)).Normal := inferInstance
  have hY : CFSG.Open.IsKGroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) :=
    CFSG.Open.IsKGroup.quotient hKX _
  have hcomp := Lemma1314.isComponentOf_barX_of_glaPComponent hHc
  have hKhat := isKHat_barX hp hKX hHc
  have hcoreK := core_barX_eq_bot hp hHc
  have hdK := mk_mem_normalizer_barX (p := p) hdX hdH
  have hdord := orderOf_mk_eq (p := p) hdX hb.dord
  have hdp : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩) ^ p = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩)
    rwa [hdord] at this
  have hH0' : GLAPComponent p (H ⊓ Cg d) H0 :=
    glaPComponent_of_le hp hH0 (le_inf hH0H (hH0.1.trans cg2_le_cg_d)) (inf_le_cg2 hHX)
  have hH0X : H0 ≤ Cg z := hH0H.trans hHX
  have hdz : IsPGroup p ↥(Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb.dord, pow_one])
  have hJ := glaPComponent_barX_inf_centralizer hp hdX hHX hdH hdz hH0'
  have eH : barOf p H ≃* ↥(barX p (Cg z) H) := quotEquivBarX hp hHX hHc.2.1
  have hH0q : CFSG.Open.IsQuasisimple (barOf p H0) := isQuasisimple_barOf_of_comp hp hH0
  have hH0core : GLAPPrimeCore p (barOf p H0) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hp2 : 2 ≠ p := by have := hb.five_le; omega
  have hH0type : (∃ n : ℕ, IsAltType n (barOf p H0 ⧸ Subgroup.center (barOf p H0))) ∨
      IsChevSimple 2 (barOf p H0 ⧸ Subgroup.center (barOf p H0)) := by
    rcases hH0t with hc | ⟨-, hA7⟩
    · exact Or.inr (isChevSimple_two_of_isChevTwo hc.2)
    · exact Or.inl ⟨7, isAltType_center_quot (by norm_num) hA7⟩
  have hclaim : ((∃ n : ℕ, IsAltType n (barOf p H ⧸ Subgroup.center (barOf p H))) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧
        IsChevSimple q (barOf p H ⧸ Subgroup.center (barOf p H)))) → False :=
    fun ht => hHM (le_M_of_type hb hI.i2319 hKP hX hHc ht)
  by_cases hcen : barX p (Cg z) H ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩} : Set (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)))
  ·
    exfalso
    have hinf : barX p (Cg z) H ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)) ⟨d, hdX⟩} :
          Set (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))) = barX p (Cg z) H := inf_eq_left.2 hcen
    have hJ' : GLAPComponent p (barX p (Cg z) H) (barX p (Cg z) H0) := by
      rw [hinf] at hJ
      exact hJ
    have hper : ⁅barX p (Cg z) H0, barX p (Cg z) H0⁆ = barX p (Cg z) H0 := glaPComponent_perfect hJ'
    have hJbot : barX p (Cg z) H0 ≠ ⊥ := ne_bot_of_quasisimple_quot (isQuasisimple_barOf_of_comp hp hJ')
    have hJK : barX p (Cg z) H0 = barX p (Cg z) H :=
      eq_of_perfect_subnormal_quasisimple hcomp.2.2 hJbot hper hJ'.2.1
    have e0 : barOf p H0 ≃* ↥(barX p (Cg z) H) :=
      (barOfBarX hp hH0X).trans (iso_of_eq_of_core hJK hcoreK)
    have eHH0 : barOf p H ≃* barOf p H0 := eH.trans e0.symm
    rcases hH0type with ⟨n, hn⟩ | hch
    · exact hclaim (Or.inl ⟨n, isAltType_center_of_equiv eHH0 hn⟩)
    · exact hclaim (Or.inr ⟨2, Nat.prime_two, hp2, isChevSimple_center_of_equiv eHH0 hch⟩)
  · have hpump0 := pumpupVia_of_setting hp hdK hdp hcen hJ
    have hpump : Lemma1314.PumpupVia p (barOf p H0) ↥(barX p (Cg z) H) (conjAutOf _ _ hdK) :=
      Lemma1314.pumpupVia_of_equiv (barOfBarX hp hH0X).symm hpump0
    rcases hH0t with hchev | ⟨hp5, hA7⟩
    · have hch2 : IsChevSimple 2 (barOf p H0 ⧸ Subgroup.center (barOf p H0)) :=
        isChevSimple_two_of_isChevTwo hchev.2
      have hnab := exists_noncomm_quot hKhat.1
      rcases catalog_cases hnab hKhat.2 with ⟨n, hn⟩ | ⟨idx, ⟨e⟩⟩ | ⟨name, hname⟩
      · exact absurd (Or.inl ⟨n, isAltType_center_of_equiv eH hn⟩) hclaim
      · have hr : idx.1.characteristic.Prime := idx.1.characteristic_prime
        have hchev : IsChevSimple idx.1.characteristic
            (↥(barX p (Cg z) H) ⧸ Subgroup.center ↥(barX p (Cg z) H)) := isChevSimple_of_lie e
        by_cases hrp : idx.1.characteristic = p
        · rw [hrp] at hchev
          obtain ⟨hch_p, hnot_inner⟩ := hI.i144 p p hp hb.five_le hp _ hKhat hcoreK hchev
            (barOf p H0) _ hpump
          obtain ⟨h57, hL2p⟩ := hI.i33 p hp hb.five_le (barOf p H0) hH0q hH0core hch2 hch_p
          have hLq := hI.i1418 p hp (by have := hb.five_le; omega) _ hKhat hcoreK hchev
            (barOf p H0) _ hL2p hpump
          refine ⟨h57, hL2p, isLpType_of_equiv eH hLq, ?_⟩
          intro hind
          obtain ⟨k, hk, hkk⟩ := innerOn_of_inducesInner hp hHc.2.1 hdX hind
          exact hnot_inner rfl (mem_innerAut_of_innerOn hdK hk hkk)
        · exact absurd (Or.inr ⟨idx.1.characteristic, hr, hrp,
            isChevSimple_center_of_equiv eH hchev⟩) hclaim
      · exact absurd (le_M_of_spor hb hI.i255 hKP hX hHc hdH hH0' hch2 ⟨name, hname⟩ hA hAr hdA hzA)
          hHM
    · exfalso
      subst hp5
      have hdis := hI.i1415 5 hp (le_refl 5) _ hKhat hcoreK
        ⟨_, Lemma1314.pumpupVia_of_equiv hA7.some hpump⟩
      rcases hdis with ⟨k, hk2, hk⟩ | ⟨-, hFi⟩
      · have : IsAltType (k * 5 + 2) (↥(barX 5 (Cg z) H) ⧸ Subgroup.center ↥(barX 5 (Cg z) H)) :=
          isAltType_center_quot (by omega) hk
        exact hclaim (Or.inl ⟨_, isAltType_center_of_equiv eH this⟩)
      · have hG := hI.iFi23 (↥(Cg z) ⧸ GLAPPrimeCore 5 ↥(Cg z)) (glaPPrimeCore_quotient_eq_bot hp)
          (barX 5 (Cg z) H) (barX 5 (Cg z) B) hcomp (isElemAbelian_barX hb.bel) hFi
        have hk3 : 3 ≤ CFSG.Open.pRank 5 B := by rw [hb.pRank_B]; have := hb.m4; omega
        exact hHM (Lemma1314.le_of_gMinusOne hp hHX hb.B_le_Cg (isPGroup_of_elemAbelian hb.bel)
          hb.normB hb.core hG hk3)


theorem h0type {p : ℕ} {H0 : Subgroup G}
    (hH0t : Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0))) :
    (∃ n : ℕ, IsAltType n (barOf p H0 ⧸ Subgroup.center (barOf p H0))) ∨
      IsChevSimple 2 (barOf p H0 ⧸ Subgroup.center (barOf p H0)) := by
  rcases hH0t with hc | ⟨-, hA7⟩
  · exact Or.inr (isChevSimple_two_of_isChevTwo hc.2)
  · exact Or.inl ⟨7, isAltType_center_quot (by norm_num) hA7⟩

structure TypeResult (p : ℕ) (X H0 H : Subgroup G) (d : G) : Prop where
  p57 : p = 5 ∨ p = 7
  lp : IsLpType 2 p (barOf p H0)
  lq : IsLpType 2 (p ^ p) (barOf p H)
  comp : GLAPComponent p X H
  H0H : H0 ≤ H
  dN : d ∈ Subgroup.normalizer (H : Set G)
  ninner : ¬ InducesInner p H d

theorem type_analysis {m p : ℕ} {B M R : Subgroup G} {d z : G} (hb : Basic m p B M R d z)
    (hI : Inputs) (hstd : GLStanding G m p) (hX : Cg z ≠ ⊤)
    {H0 : Subgroup G} (hH0 : GLAPComponent p (Cg2 d z) H0) (hH0M : ¬ H0 ≤ M)
    (hH0t : Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0)))
    {A : Subgroup G} (hA : IsSCp p (Cg z) A) (hAr : CFSG.Open.pRank p A = 3) (hdA : d ∈ A)
    (hzA : z ∈ A) {H : Subgroup G} (hHdef : H = ⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0) :
    TypeResult p (Cg z) H0 H d := by
  have hp := hb.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := hb.five_le; omega
  have hH0H : H0 ≤ H := by
    rw [hHdef]
    exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (le_of_eq (gLBConj_one H0).symm)
  rcases hI.i183 p hp hp2 G hstd.simple hstd.nonabelian hstd.kProper d z hb.dord hb.zo hb.dz H0
    hH0 with ⟨L, hL, hHL, hdL⟩ | ⟨L, hL, hinj, hcyc, hHL⟩
  · have hLH : H = L := hHdef.trans hHL
    have hHc : GLAPComponent p (Cg z) H := hLH ▸ hL
    have hdH : d ∈ Subgroup.normalizer (H : Set G) :=
      mem_normalizer_iff_gLBConj_eq.2 (hLH ▸ hdL)
    have hHM : ¬ H ≤ M := fun h => hH0M (hH0H.trans h)
    obtain ⟨h57, hlp, hlq, hni⟩ :=
      single_case hb hI hstd hX hHc hdH hH0H hH0 hHM hH0t hA hAr hdA hzA
    exact ⟨h57, hlp, hlq, hHc, hH0H, hdH, hni⟩
  · exfalso
    have hdiag := hI.iDiag p hp hp2 G hstd.simple hstd.nonabelian hstd.kProper d z hb.dord hb.zo
      hb.dz H0 hH0 L hL hinj hcyc hHL
    have hLM : ∀ i, L i ≤ M := fun i => by
      obtain ⟨e⟩ := hdiag i
      rcases h0type hH0t with ⟨n, hn⟩ | hch
      · exact le_M_of_type hb hI.i2319 hstd.kProper hX (hL i)
          (Or.inl ⟨n, Lemma1314.isAltType_of_equiv e.symm hn⟩)
      · exact le_M_of_type hb hI.i2319 hstd.kProper hX (hL i)
          (Or.inr ⟨2, Nat.prime_two, hp2.symm, isChevSimple_of_equiv e.symm hch⟩)
    have hHM : H ≤ M := by
      rw [hHdef, hHL]
      exact iSup_le hLM
    exact hH0M (hH0H.trans hHM)

end TypeAnalysis


section Structure

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_zpowers {p : ℕ} {z : G} (hz : z ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers z) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

theorem inf_zpowers_eq_bot {p : ℕ} [hp : Fact p.Prime] {z : G} (hz : orderOf z = p)
    {E : Subgroup G} (hzE : z ∉ E) : E ⊓ Subgroup.zpowers z = ⊥ := by
  haveI : Fact (Nat.card (Subgroup.zpowers z)).Prime :=
    ⟨by rw [Nat.card_zpowers, hz]; exact hp.out⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (E.subgroupOf (Subgroup.zpowers z)) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : ↥(Subgroup.zpowers z)) ∈ E.subgroupOf (Subgroup.zpowers z) :=
      Subgroup.mem_subgroupOf.2 hx.1
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    have : (⟨z, Subgroup.mem_zpowers z⟩ : ↥(Subgroup.zpowers z)) ∈
        E.subgroupOf (Subgroup.zpowers z) := by
      rw [h]
      exact Subgroup.mem_top _
    exact hzE (Subgroup.mem_subgroupOf.1 this)

theorem card_sup_of_commute {E F : Subgroup G} (hEF : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a)
    (hdis : E ⊓ F = ⊥) : Nat.card ↥(E ⊔ F) = Nat.card E * Nat.card F := by
  have hEN : E ≤ Subgroup.normalizer (F : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer (F : Set G)
      (Subgroup.mem_centralizer_iff.2 fun f hf => (hEF e he f hf).symm)
  let f : E × F → ↥(E ⊔ F) := fun ab => ⟨(ab.1 : G) * ab.2, Subgroup.mul_mem_sup ab.1.2 ab.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * ((a : G) * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have h3 : ((a' : G)⁻¹ * a) ∈ E ⊓ F :=
      ⟨E.mul_mem (E.inv_mem a'.2) a.2, h2 ▸ F.mul_mem b'.2 (F.inv_mem b.2)⟩
    rw [hdis, Subgroup.mem_bot] at h3
    have ha : (a : G) = a' := (inv_mul_eq_one.1 h3).symm
    have hb : (b : G) = b' := by
      rw [ha] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ ((E ⊔ F : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E F hEN] at hx'
    obtain ⟨e, he, g, hg, rfl⟩ := hx'
    exact ⟨(⟨e, he⟩, ⟨g, hg⟩), rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm, Nat.card_prod]

theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Group K] {k : K}
    (hk : k ^ p = 1) : IsPGroup p (Subgroup.zpowers k) := by
  rcases (Nat.dvd_prime hp.out).1 (orderOf_dvd_of_pow_eq_one hk) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem isElemAbelian_range {p : ℕ} {A G' : Type*} [Group A] [Group G'] (f : A →* G')
    (hc : ∀ x y : A, x * y = y * x) (hp : ∀ x : A, x ^ p = 1) : IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G') * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, hc]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hp, map_one]

theorem barAut_of_mem {p : ℕ} {H : Subgroup G} {x : G} (hx : x ∈ H) :
    barAut p H ⟨x, Subgroup.le_normalizer hx⟩ =
      MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨x, hx⟩) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
    have h : (H.normalizerMonoidHom ⟨x, Subgroup.le_normalizer hx⟩ y : ↥H) =
        ⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹ := Subtype.ext rfl
    rw [h, MulAut.conj_apply]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem isElemAbelian_of_barX {p : ℕ} (hp : p.Prime) {C E : Subgroup G} (hE : IsPGroup p E)
    (hEC : E ≤ C) (h : IsElemAbelian p (barX p C E)) : IsElemAbelian p E := by
  have hfi := injective_barX_comp hp hE hEC
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (E.subgroupOf C).subtype with hf
  have hmem : ∀ a : ↥(E.subgroupOf C), f a ∈ barX p C E := fun a => ⟨a, a.2, rfl⟩
  have key : ∀ a b : ↥(E.subgroupOf C), a * b = b * a := by
    intro a b
    apply hfi
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (h.1.is_comm.comm ⟨f a, hmem a⟩ ⟨f b, hmem b⟩)
  have key2 : ∀ a : ↥(E.subgroupOf C), a ^ p = 1 := by
    intro a
    apply hfi
    rw [map_pow, map_one]
    exact h.2 _ (hmem a)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have := congrArg (fun t : ↥(E.subgroupOf C) => ((t : ↥C) : G))
      (key ⟨⟨a, hEC a.2⟩, Subgroup.mem_subgroupOf.2 a.2⟩ ⟨⟨b, hEC b.2⟩, Subgroup.mem_subgroupOf.2 b.2⟩)
    exact this
  · have := congrArg (fun t : ↥(E.subgroupOf C) => ((t : ↥C) : G))
      (key2 ⟨⟨x, hEC hx⟩, Subgroup.mem_subgroupOf.2 hx⟩)
    exact this

structure Sit (m p : ℕ) (B M R : Subgroup G) (d z : G) (H : Subgroup G) : Prop where
  hb : Basic m p B M R d z
  comp : GLAPComponent p (Cg z) H
  dN : d ∈ Subgroup.normalizer (H : Set G)
  BN : B ≤ Subgroup.normalizer (H : Set G)
  cb : centBar p B H = Subgroup.zpowers z
  ninner : ¬ InducesInner p H d
  L2 : L2Facts p (barOf p H)

section SitLemmas

variable {m p : ℕ} {B M R : Subgroup G} {d z : G} {H : Subgroup G}

theorem Sit.z_not_mem (hs : Sit m p B M R d z H) : z ∉ H := by
  intro hz
  haveI : Fact p.Prime := ⟨hs.hb.prime⟩
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨z, hz⟩ ∈ Subgroup.center (barOf p H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      show (QuotientGroup.mk' (GLAPPrimeCore p ↥H)) (x * ⟨z, hz⟩) =
        (QuotientGroup.mk' (GLAPPrimeCore p ↥H)) (⟨z, hz⟩ * x)
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (hs.comp.1 x.2)
  rw [hs.L2.1, Subgroup.mem_bot] at hmem
  have := orderOf_mk_eq (p := p) hz hs.hb.zo
  rw [hmem, orderOf_one] at this
  exact hs.hb.prime.ne_one this.symm

theorem Sit.exists_P0 (hs : Sit m p B M R d z H) :
    ∃ P0 : Subgroup G, P0 ≤ H ∧ IsElemAbelian p P0 ∧ Nat.card P0 = p ^ p := by
  haveI : Fact p.Prime := ⟨hs.hb.prime⟩
  haveI : (GLAPPrimeCore p ↥H).Normal := inferInstance
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥H) :=
    (Nat.Prime.coprime_iff_not_dvd hs.hb.prime).1 CFSG.pPrimeCore_coprime_card
  obtain ⟨-, hP, ⟨S, hSp, hScard⟩, -⟩ := hs.L2
  obtain ⟨T, hT, hTmap, hTcard⟩ :=
    exists_elemAbelian_lift (GLAPPrimeCore p ↥H) hN (hP S hSp).1
  refine ⟨T.map H.subtype, Subgroup.map_subtype_le T,
    CFSG.SectionRank.isElemAbelian_map hT _, ?_⟩
  rw [Subgroup.card_map_of_injective H.subtype_injective, hTcard, hScard]

theorem Sit.m_ge (hs : Sit m p B M R d z H) : p + 1 ≤ m := by
  have hb := hs.hb
  haveI : Fact p.Prime := ⟨hb.prime⟩
  obtain ⟨P0, hP0H, hP0el, hP0card⟩ := hs.exists_P0
  have hzP0 : z ∉ P0 := fun h => hs.z_not_mem (hP0H h)
  have hdis : P0 ⊓ Subgroup.zpowers z = ⊥ := inf_zpowers_eq_bot hb.zo hzP0
  have hcomm : ∀ a ∈ P0, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
    have hc : Commute a z := Subgroup.mem_centralizer_singleton_iff.1 (hs.comp.1 (hP0H ha))
    exact (Commute.zpow_right hc i).eq
  have hz1 : z ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hb.zo] at this
  have hel := elemAbelian_sup hP0el (isElemAbelian_zpowers hz1) hcomm
  have h1 := card_le_of_sylow hb.rsyl (k := m) (fun E hER hE => ?_) hel
  · rw [card_sup_of_commute hcomm hdis, hP0card, Nat.card_zpowers, hb.zo, ← pow_succ] at h1
    exact (Nat.pow_le_pow_iff_right hb.prime.one_lt).1 h1
  · exact hb.rk E hE

@[expose] noncomputable def phiB (p : ℕ) {B H : Subgroup G}
    (hBH : B ≤ Subgroup.normalizer (H : Set G)) : ↥B →* MulAut (barOf p H) :=
  (barAut p H).comp (Subgroup.inclusion hBH)

theorem phiB_mk (p : ℕ) {B H : Subgroup G} (hBH : B ≤ Subgroup.normalizer (H : Set G)) (b : ↥B)
    (y : ↥H) : phiB p hBH b (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨(b : G) * y * (b : G)⁻¹, by
        have := (Subgroup.mem_normalizer_iff.1 (hBH b.2) y).1 y.2
        exact this⟩ :=
  CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk p H _ y

theorem phiB_eq_one_iff (p : ℕ) {B H : Subgroup G} (hBH : B ≤ Subgroup.normalizer (H : Set G))
    (b : ↥B) : phiB p hBH b = 1 ↔ (b : G) ∈ centBar p B H := by
  constructor
  · intro h
    exact ⟨⟨⟨b, hBH b.2⟩, h, rfl⟩, b.2⟩
  · rintro ⟨⟨n, hn, hnb⟩, -⟩
    have : n = Subgroup.inclusion hBH b := Subtype.ext hnb
    rw [this] at hn
    exact hn

theorem Sit.card_ker (hs : Sit m p B M R d z H) : Nat.card (phiB p hs.BN).ker = p := by
  have h : (phiB p hs.BN).ker.map B.subtype = centBar p B H := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (phiB_eq_one_iff p hs.BN b).1 hb
    · intro hx
      exact ⟨⟨x, hx.2⟩, (phiB_eq_one_iff p hs.BN ⟨x, hx.2⟩).2 hx, rfl⟩
  have hc : Nat.card ((phiB p hs.BN).ker.map B.subtype) = Nat.card (phiB p hs.BN).ker :=
    Subgroup.card_map_of_injective B.subtype_injective
  rw [h, hs.cb, Nat.card_zpowers, hs.hb.zo] at hc
  exact hc.symm

theorem Sit.m_eq_and_inner (hs : Sit m p B M R d z H) :
    m = p + 1 ∧ (phiB p hs.BN).range ≤ innerAut (barOf p H) := by
  have hb := hs.hb
  haveI : Fact p.Prime := ⟨hb.prime⟩
  have hge := hs.m_ge
  obtain ⟨-, -, -, hE, -⟩ := hs.L2
  have hel : IsElemAbelian p (phiB p hs.BN).range :=
    isElemAbelian_range _ (fun x y => Subtype.ext (comm_of_mem hb.bel x.2 y.2))
      (fun x => Subtype.ext (hb.bel.2 x.1 x.2))
  obtain ⟨hle, hinn⟩ := hE _ hel
  have hker := Subgroup.card_ker_mul_card_range (phiB p hs.BN)
  rw [hs.card_ker, hb.bcard] at hker
  have hrange : Nat.card (phiB p hs.BN).range = p ^ (m - 1) := by
    have : p * p ^ (m - 1) = p ^ m := by
      rw [← pow_succ']
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left hb.prime.pos (hker.trans this.symm)
  rw [hrange] at hle
  have hm1 : m - 1 ≤ p := (Nat.pow_le_pow_iff_right hb.prime.one_lt).1 hle
  have hm : m = p + 1 := by omega
  refine ⟨hm, hinn ?_⟩
  rw [hrange, hm]
  rfl


theorem mem_center_of_conj_eq_one {K : Type*} [Group K] {g : K} (h : MulAut.conj g = 1) :
    g ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro y
  have := congrArg (fun f : MulAut K => f y) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem barX_maximal {p : ℕ} (hp : p.Prime) {H P : Subgroup G} (hPH : P ≤ H) (hPp : IsPGroup p P)
    (hPmax : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → P ≤ Q → Q = P)
    (hel : ∀ S : Subgroup (barOf p H), IsPGroup p S → IsElemAbelian p S)
    {S : Subgroup (barOf p H)} (hS : IsPGroup p S) (hPS : barX p H P ≤ S) :
    S = barX p H P := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (GLAPPrimeCore p ↥H).Normal := inferInstance
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥H) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hAp : IsPGroup p ↥(P.subgroupOf H) := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hPS' : (P.subgroupOf H).map (QuotientGroup.mk' (GLAPPrimeCore p ↥H)) ≤ S := hPS
  obtain ⟨T, hPT, hTel, hTmap⟩ :=
    exists_elemAbelian_lift_above (GLAPPrimeCore p ↥H) hN (hel S hS) hAp hPS'
  have hTG : IsPGroup p ↥(T.map H.subtype) :=
    isPGroup_of_elemAbelian (CFSG.SectionRank.isElemAbelian_map hTel _)
  have hPle : P ≤ T.map H.subtype := fun x hx =>
    ⟨⟨x, hPH hx⟩, hPT (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hTeq : T.map H.subtype = P := hPmax _ (Subgroup.map_subtype_le T) hTG hPle
  have hT' : T = P.subgroupOf H := by
    rw [← hTeq]
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective T).symm
  rw [← hTmap, hT']
  rfl

theorem Sit.exists_k (hs : Sit m p B M R d z H) {P : Subgroup G} (hPH : P ≤ H)
    (hPp : IsPGroup p P) (hPmax : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → P ≤ Q → Q = P)
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) {b : G} (hb : b ∈ B) :
    ∃ k ∈ barX p H P, phiB p hs.BN ⟨b, hb⟩ = MulAut.conj k := by
  have hbb := hs.hb
  haveI : Fact p.Prime := ⟨hbb.prime⟩
  obtain ⟨hZ, hP2, -, -, -, -⟩ := hs.L2
  have hel : ∀ S : Subgroup (barOf p H), IsPGroup p S → IsElemAbelian p S :=
    fun S hS => (hP2 S hS).1
  obtain ⟨-, hinn⟩ := hs.m_eq_and_inner
  obtain ⟨k, hk⟩ := hinn ⟨⟨b, hb⟩, rfl⟩
  have hfwd : ∀ (b' : ↥B) (y : barOf p H), y ∈ barX p H P → phiB p hs.BN b' y ∈ barX p H P := by
    intro b' y hy
    obtain ⟨⟨x, hxH⟩, hxP, rfl⟩ := hy
    have hxP' : x ∈ P := Subgroup.mem_subgroupOf.1 hxP
    show phiB p hs.BN b' (QuotientGroup.mk ⟨x, hxH⟩) ∈ _
    rw [phiB_mk]
    exact ⟨_, Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.1 (hBP b'.2) x).1 hxP'), rfl⟩
  have hbwd : ∀ y : barOf p H, phiB p hs.BN ⟨b, hb⟩ y ∈ barX p H P → y ∈ barX p H P := by
    intro y hy
    have := hfwd (⟨b, hb⟩ : ↥B)⁻¹ _ hy
    rwa [map_inv, MulAut.inv_apply_self] at this
  have hkN : k ∈ Subgroup.normalizer ((barX p H P : Subgroup (barOf p H)) : Set (barOf p H)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← MulAut.conj_apply, hk]
    exact ⟨fun h => hfwd _ y h, hbwd y⟩
  have hkp : k ^ p = 1 := by
    have h1 : (MulAut.conj k) ^ p = 1 := by
      rw [hk, ← map_pow]
      have : (⟨b, hb⟩ : ↥B) ^ p = 1 := Subtype.ext (hbb.bel.2 b hb)
      rw [this, map_one]
    have h2 : MulAut.conj (k ^ p) = 1 := by
      rw [map_pow]
      exact h1
    have := mem_center_of_conj_eq_one h2
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  have hPbp : IsPGroup p ↥(barX p H P) :=
    (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm).map _
  have hzk : IsPGroup p ↥(Subgroup.zpowers k) := isPGroup_zpowers_of_pow_eq_one hkp
  have hsup : IsPGroup p ↥(Subgroup.zpowers k ⊔ barX p H P) :=
    hzk.to_sup_of_normal_right' hPbp ((Subgroup.zpowers_le).2 hkN)
  have heq := barX_maximal hbb.prime hPH hPp hPmax hel hsup le_sup_right
  refine ⟨k, ?_, hk.symm⟩
  have : k ∈ Subgroup.zpowers k ⊔ barX p H P := Subgroup.mem_sup_left (Subgroup.mem_zpowers k)
  rwa [heq] at this

theorem Sit.B_comm_P (hs : Sit m p B M R d z H) {P : Subgroup G} (hPH : P ≤ H)
    (hPp : IsPGroup p P) (hPmax : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → P ≤ Q → Q = P)
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) {b : G} (hb : b ∈ B) {x : G} (hx : x ∈ P) :
    b * x = x * b := by
  have hbb := hs.hb
  haveI : Fact p.Prime := ⟨hbb.prime⟩
  obtain ⟨-, hP2, -, -, -, -⟩ := hs.L2
  have hel : ∀ S : Subgroup (barOf p H), IsPGroup p S → IsElemAbelian p S :=
    fun S hS => (hP2 S hS).1
  obtain ⟨k, hkP, hk⟩ := hs.exists_k hPH hPp hPmax hBP hb
  have hPbp : IsPGroup p ↥(barX p H P) :=
    (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm).map _
  have hPel := hel _ hPbp
  have hxH : x ∈ H := hPH hx
  have hxbar : QuotientGroup.mk (⟨x, hxH⟩ : ↥H) ∈ barX p H P :=
    ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have h1 : phiB p hs.BN ⟨b, hb⟩ (QuotientGroup.mk ⟨x, hxH⟩) = QuotientGroup.mk ⟨x, hxH⟩ := by
    rw [hk, MulAut.conj_apply, comm_of_mem hPel hkP hxbar, mul_inv_cancel_right]
  rw [phiB_mk] at h1
  have hfi := injective_barX_comp hbb.prime hPp hPH
  have h2 := hfi (a₁ := ⟨⟨b * x * b⁻¹, by
      have := (Subgroup.mem_normalizer_iff.1 (hs.BN hb) x).1 hxH
      exact this⟩, Subgroup.mem_subgroupOf.2
        ((Subgroup.mem_normalizer_iff.1 (hBP hb) x).1 hx)⟩)
    (a₂ := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.2 hx⟩) h1
  have h3 : b * x * b⁻¹ = x := congrArg (fun t : ↥(P.subgroupOf H) => ((t : ↥H) : G)) h2
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3


theorem Sit.H_comm_z (hs : Sit m p B M R d z H) :
    ∀ a ∈ H, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
  intro a ha b hb'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
  have hc : Commute a z := Subgroup.mem_centralizer_singleton_iff.1 (hs.comp.1 ha)
  exact (Commute.zpow_right hc i).eq

theorem Sit.exists_P (hs : Sit m p B M R d z H) :
    ∃ P : Subgroup G, P ≤ H ∧ IsPGroup p P ∧
      (∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → P ≤ Q → Q = P) ∧
      B ≤ Subgroup.normalizer (P : Set G) ∧ IsElemAbelian p P ∧ P ≤ B ∧
      B = P ⊔ Subgroup.zpowers z ∧ P ⊓ Subgroup.zpowers z = ⊥ ∧ B ⊓ H = P ∧
      Nat.card P = p ^ p := by
  have hbb := hs.hb
  haveI : Fact p.Prime := ⟨hbb.prime⟩
  have hBp : IsPGroup p B := isPGroup_of_elemAbelian hbb.bel
  obtain ⟨P, hPH, hPp, hPmax, hBP⟩ := exists_normalized_sylow hBp hs.BN
  obtain ⟨-, hP2, -, -, -, -⟩ := hs.L2
  have hel : ∀ S : Subgroup (barOf p H), IsPGroup p S → IsElemAbelian p S :=
    fun S hS => (hP2 S hS).1
  have hPbp : IsPGroup p ↥(barX p H P) :=
    (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm).map _
  have hPel : IsElemAbelian p P := isElemAbelian_of_barX hbb.prime hPp hPH (hel _ hPbp)
  have hcomm : ∀ b ∈ B, ∀ x ∈ P, b * x = x * b := fun b hb x hx =>
    hs.B_comm_P hPH hPp hPmax hBP hb hx
  have hPB : P ≤ B := by
    have hsup := elemAbelian_sup hbb.bel hPel hcomm
    have := hbb.bsc.2.2 (B ⊔ P) le_top hsup le_sup_left
    exact le_sup_right.trans this.le
  have hBle : B ≤ P ⊔ Subgroup.zpowers z := by
    intro b hb
    obtain ⟨k, hkP, hk⟩ := hs.exists_k hPH hPp hPmax hBP hb
    obtain ⟨⟨x, hxH⟩, hxP, hxk⟩ := hkP
    have hxP' : x ∈ P := Subgroup.mem_subgroupOf.1 hxP
    have hxB : x ∈ B := hPB hxP'
    have hφx : phiB p hs.BN ⟨x, hxB⟩ = MulAut.conj k := by
      have := barAut_of_mem (p := p) hxH
      rw [← hxk]
      exact this
    have hone : phiB p hs.BN ⟨x⁻¹ * b, B.mul_mem (B.inv_mem hxB) hb⟩ = 1 := by
      have : (⟨x⁻¹ * b, B.mul_mem (B.inv_mem hxB) hb⟩ : ↥B) = (⟨x, hxB⟩ : ↥B)⁻¹ * ⟨b, hb⟩ := rfl
      rw [this, map_mul, map_inv, hφx, hk, inv_mul_cancel]
    have hcb : x⁻¹ * b ∈ Subgroup.zpowers z := by
      have := (phiB_eq_one_iff p hs.BN _).1 hone
      rw [hs.cb] at this
      exact this
    have : b = x * (x⁻¹ * b) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hxP' hcb
  have hBeq : B = P ⊔ Subgroup.zpowers z :=
    le_antisymm hBle (sup_le hPB ((Subgroup.zpowers_le).2 hbb.zB))
  have hdis : P ⊓ Subgroup.zpowers z = ⊥ :=
    inf_zpowers_eq_bot hbb.zo (fun h => hs.z_not_mem (hPH h))
  have hHz : H ⊓ Subgroup.zpowers z = ⊥ := inf_zpowers_eq_bot hbb.zo hs.z_not_mem
  have hPz : ∀ a ∈ P, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := fun a ha b hb =>
    hs.H_comm_z a (hPH ha) b hb
  have hBH : B ⊓ H = P := by
    apply le_antisymm
    · rintro x ⟨hxB, hxH⟩
      rw [hBeq] at hxB
      have hPN : P ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := fun e he =>
        Subgroup.centralizer_le_normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)
          (Subgroup.mem_centralizer_iff.2 fun f hf => (hPz e he f hf).symm)
      have hx' : x ∈ ((P ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := hxB
      rw [Subgroup.coe_mul_of_left_le_normalizer_right P (Subgroup.zpowers z) hPN] at hx'
      obtain ⟨y, hy, w, hw, rfl⟩ := hx'
      have hwH : w ∈ H := by
        have : w = y⁻¹ * (y * w) := by group
        rw [this]
        exact H.mul_mem (H.inv_mem (hPH hy)) hxH
      have : w ∈ H ⊓ Subgroup.zpowers z := ⟨hwH, hw⟩
      rw [hHz, Subgroup.mem_bot] at this
      rw [this]
      show y * 1 ∈ P
      rw [mul_one]
      exact hy
    · exact le_inf hPB hPH
  have hcard : Nat.card P = p ^ p := by
    have h1 := card_sup_of_commute hPz hdis
    rw [← hBeq, hbb.bcard, Nat.card_zpowers, hbb.zo, hs.m_eq_and_inner.1, pow_succ] at h1
    exact (Nat.eq_of_mul_eq_mul_right hbb.prime.pos h1).symm
  exact ⟨P, hPH, hPp, hPmax, hBP, hPel, hPB, hBeq, hdis, hBH, hcard⟩


theorem conj_mem_Cg {z g x : G}
    (hg : g ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) (hx : x ∈ Cg z) :
    g * x * g⁻¹ ∈ Cg z := by
  have hw : g⁻¹ * z * g ∈ Subgroup.zpowers z := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) z).1 (Subgroup.mem_zpowers z)
    simpa using this
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hc : Commute x z := (Subgroup.mem_centralizer_singleton_iff.1 hx)
  have hxw : x * (g⁻¹ * z * g) = (g⁻¹ * z * g) * x := by
    rw [← hi]
    exact (Commute.zpow_right hc i).eq
  rw [Subgroup.mem_centralizer_singleton_iff]
  show g * x * g⁻¹ * z = z * (g * x * g⁻¹)
  calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [hxw]
    _ = z * (g * x * g⁻¹) := by group

theorem barX_comm_of_commutator_le {p : ℕ} {X H H' : Subgroup G} (hHX : H ≤ X) (hH'X : H' ≤ X)
    (h : ⁅H, H'⁆ ≤ GLAPPrimeCoreOf p X) :
    ∀ a ∈ barX p X H, ∀ b ∈ barX p X H', a * b = b * a := by
  rintro _ ⟨⟨x, hxX⟩, hxH, rfl⟩ _ ⟨⟨x', hx'X⟩, hx'H, rfl⟩
  have hx : x ∈ H := Subgroup.mem_subgroupOf.1 hxH
  have hx' : x' ∈ H' := Subgroup.mem_subgroupOf.1 hx'H
  have hc : x * x' * x⁻¹ * x'⁻¹ ∈ GLAPPrimeCoreOf p X := h (Subgroup.commutator_mem_commutator hx hx')
  obtain ⟨u, hu, hux⟩ := hc
  have hu' : u = ⟨x, hxX⟩ * ⟨x', hx'X⟩ * (⟨x, hxX⟩ : ↥X)⁻¹ * (⟨x', hx'X⟩ : ↥X)⁻¹ := Subtype.ext hux
  have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) u = 1 :=
    (QuotientGroup.eq_one_iff u).2 hu
  rw [hu', map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  set a := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩
  set b := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x', hx'X⟩
  have h2 : a * b * a⁻¹ * b⁻¹ = 1 := h1
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h2, one_mul]

theorem Sit.normalizer_zpowers_le (hs : Sit m p B M R d z H) {g : G}
    (hg : g ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  have hbb := hs.hb
  have hp := hbb.prime
  haveI : Fact p.Prime := ⟨hp⟩
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  have hgX : g ∈ Subgroup.normalizer ((Cg z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => conj_mem_Cg hg hx, fun hx => by
      have h1 := conj_mem_Cg (inv_mem hg) hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at h1⟩
  have hH' : GLAPComponent p (Cg z) (GLBConj g H) := by
    have := glaPComponent_gLBConj hs.comp g
    rwa [mem_normalizer_iff_gLBConj_eq.1 hgX] at this
  have hcomm := CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne hp
    hs.comp hH' (fun h => hne h.symm)
  obtain ⟨P, hPH, hPp, -, -, hPel, -, -, -, -, hPcard⟩ := hs.exists_P
  have hHX : H ≤ Cg z := hs.comp.1
  have hH'X : GLBConj g H ≤ Cg z := hH'.1
  set P' : Subgroup G := GLBConj g P with hP'
  have hP'H : P' ≤ GLBConj g H := gLBConj_mono g hPH
  have hP'p : IsPGroup p ↥P' := hPp.of_equiv (conjEquiv g P)
  have hP'el : IsElemAbelian p P' :=
    CFSG.SectionRank.isElemAbelian_map hPel (MulAut.conj g⁻¹).toMonoidHom
  have hP'card : Nat.card P' = p ^ p := by
    rw [hP', card_gLBConj', hPcard]
  have hPX : P ≤ Cg z := hPH.trans hHX
  have hP'X : P' ≤ Cg z := hP'H.trans hH'X
  have hel1 : IsElemAbelian p (barX p (Cg z) P) := isElemAbelian_barX hPel
  have hel2 : IsElemAbelian p (barX p (Cg z) P') := isElemAbelian_barX hP'el
  have hc1 : Nat.card (barX p (Cg z) P) = p ^ p := by rw [card_barX_eq hp hPp hPX, hPcard]
  have hc2 : Nat.card (barX p (Cg z) P') = p ^ p := by rw [card_barX_eq hp hP'p hP'X, hP'card]
  have hcomm' := barX_comm_of_commutator_le hHX hH'X hcomm
  have hsub : ∀ a ∈ barX p (Cg z) P, ∀ b ∈ barX p (Cg z) P', a * b = b * a := fun a ha b hb =>
    hcomm' a (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2
      (hPH (Subgroup.mem_subgroupOf.1 hx))) ha) b
      (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2
        (hP'H (Subgroup.mem_subgroupOf.1 hx))) hb)
  have hcen : Subgroup.center ↥(barX p (Cg z) H) = ⊥ := by
    have e := quotEquivBarX hp hHX hs.comp.2.1
    have h1 := Subgroup.map_center_eq e
    rw [hs.L2.1, Subgroup.map_bot] at h1
    exact h1.symm
  have hdis : barX p (Cg z) P ⊓ barX p (Cg z) P' = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hu1, hu2⟩
    have hu1' : u ∈ barX p (Cg z) H := Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2
      (hPH (Subgroup.mem_subgroupOf.1 hx))) hu1
    have hu2' : u ∈ barX p (Cg z) (GLBConj g H) := Subgroup.map_mono (fun x hx =>
      Subgroup.mem_subgroupOf.2 (hP'H (Subgroup.mem_subgroupOf.1 hx))) hu2
    have hmem : (⟨u, hu1'⟩ : ↥(barX p (Cg z) H)) ∈ Subgroup.center ↥(barX p (Cg z) H) := by
      rw [Subgroup.mem_center_iff]
      intro a
      exact Subtype.ext (hcomm' a a.2 u hu2')
    rw [hcen, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  have hsup := elemAbelian_sup hel1 hel2 hsub
  have hle := card_le_barX (p := p) (X := Cg z) (k := m) hbb.rk hsup
  rw [card_sup_of_commute hsub hdis, hc1, hc2, ← pow_add,
    hs.m_eq_and_inner.1] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  have := hbb.five_le
  omega


theorem mem_normalizer_zpowers_of_commute {r z : G} (h : r * z = z * r) :
    r ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
  Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun x hx => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact (Commute.zpow_right (h : Commute r z) i).eq.symm)

theorem Sit.R_le_normalizer (hs : Sit m p B M R d z H) {r : G} (hr : r ∈ R) :
    r ∈ Subgroup.normalizer (H : Set G) :=
  hs.normalizer_zpowers_le (mem_normalizer_zpowers_of_commute (hs.hb.zR r hr))

theorem Sit.R_facts (hs : Sit m p B M R d z H) :
    ∃ P : Subgroup G, P ≤ H ∧ IsPGroup p P ∧
      (∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → P ≤ Q → Q = P) ∧
      IsElemAbelian p P ∧ P ≤ B ∧ B = P ⊔ Subgroup.zpowers z ∧
      P ⊓ Subgroup.zpowers z = ⊥ ∧ B ⊓ H = P ∧ Nat.card P = p ^ p ∧ R ⊓ H = P ∧
      R ≤ Subgroup.normalizer (P : Set G) ∧ R ≤ Subgroup.normalizer (B : Set G) := by
  have hbb := hs.hb
  haveI : Fact p.Prime := ⟨hbb.prime⟩
  obtain ⟨P, hPH, hPp, hPmax, hBP, hPel, hPB, hBeq, hdis, hBH, hcard⟩ := hs.exists_P
  have hRH : R ⊓ H = P :=
    hPmax (R ⊓ H) inf_le_right (IsPGroup.to_le hbb.rsyl.2.1 inf_le_left)
      (le_inf (hPB.trans hbb.bR) hPH)
  have hRP : R ≤ Subgroup.normalizer (P : Set G) := by
    intro r hr
    have hrH := hs.R_le_normalizer hr
    have hRn : ∀ r' ∈ R, ∀ x ∈ P, r' * x * r'⁻¹ ∈ P := by
      intro r' hr' x hx
      have hx' : x ∈ R ⊓ H := hRH ▸ hx
      rw [← hRH]
      exact ⟨R.mul_mem (R.mul_mem hr' hx'.1) (R.inv_mem hr'),
        (Subgroup.mem_normalizer_iff.1 (hs.R_le_normalizer hr') x).1 hx'.2⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hRn r hr x, fun hx => ?_⟩
    have := hRn r⁻¹ (R.inv_mem hr) _ hx
    simpa [mul_assoc] using this
  refine ⟨P, hPH, hPp, hPmax, hPel, hPB, hBeq, hdis, hBH, hcard, hRH, hRP, ?_⟩
  have key : ∀ r' ∈ R, ∀ x ∈ B, r' * x * r'⁻¹ ∈ B := by
    intro r' hr' x hx
    have hle : P ⊔ Subgroup.zpowers z ≤
        (P ⊔ Subgroup.zpowers z).comap (MulAut.conj r').toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hRP hr') x).1 hx)
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        have h1 : r' * z ^ i * r'⁻¹ = z ^ i :=
          mul_inv_eq_iff_eq_mul.2 (Commute.zpow_right (hbb.zR r' hr' : Commute r' z) i).eq
        show r' * z ^ i * r'⁻¹ ∈ P ⊔ Subgroup.zpowers z
        rw [h1]
        exact Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i)
    have := hle (hBeq ▸ hx)
    rw [hBeq]
    exact this
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key r hr x, fun hx => ?_⟩
  have := key r⁻¹ (R.inv_mem hr) _ hx
  simpa [mul_assoc] using this


theorem Sit.centBar_comm (hs : Sit m p B M R d z H) {P : Subgroup G} (hPH : P ≤ H)
    (hPp : IsPGroup p P) (hRP : R ≤ Subgroup.normalizer (P : Set G)) {f : G}
    (hf : f ∈ centBar p R H) {x : G} (hx : x ∈ P) : f * x = x * f := by
  have hbb := hs.hb
  obtain ⟨⟨n, hn, hnf⟩, hfR⟩ := hf
  have hn1 : barAut p H n = 1 := hn
  have hxH := hPH hx
  have hfN := hs.R_le_normalizer hfR
  have hfH : f * x * f⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hfN x).1 hxH
  have hfP : f * x * f⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hRP hfR) x).1 hx
  have h1 := congrArg (fun φ : MulAut (barOf p H) => φ (QuotientGroup.mk ⟨x, hxH⟩)) hn1
  simp only [MulAut.one_apply] at h1
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at h1
  have h3 : (H.normalizerMonoidHom n ⟨x, hxH⟩ : ↥H) = ⟨f * x * f⁻¹, hfH⟩ :=
    Subtype.ext (by rw [coe_normalizerMonoidHom]; rw [show (n : G) = f from hnf])
  rw [h3] at h1
  have hfi := injective_barX_comp hbb.prime hPp hPH
  have h2 := hfi (a₁ := ⟨⟨f * x * f⁻¹, hfH⟩, Subgroup.mem_subgroupOf.2 hfP⟩)
    (a₂ := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.2 hx⟩) h1
  have h4 : f * x * f⁻¹ = x := congrArg (fun t : ↥(P.subgroupOf H) => ((t : ↥H) : G)) h2
  rw [mul_inv_eq_iff_eq_mul] at h4
  exact h4

theorem Sit.centBar_inf_P (hs : Sit m p B M R d z H) {P : Subgroup G} (hPH : P ≤ H)
    (hPp : IsPGroup p P) {u : G} (hu : u ∈ centBar p R H) (huP : u ∈ P) : u = 1 := by
  have hbb := hs.hb
  obtain ⟨⟨n, hn, hnu⟩, -⟩ := hu
  have huH := hPH huP
  have hn1 : barAut p H n = 1 := hn
  have hnu' : n = ⟨u, Subgroup.le_normalizer huH⟩ := Subtype.ext hnu
  rw [hnu', barAut_of_mem huH] at hn1
  have hmem := mem_center_of_conj_eq_one hn1
  rw [hs.L2.1, Subgroup.mem_bot] at hmem
  have hfi := injective_barX_comp hbb.prime hPp hPH
  have h2 := hfi (a₁ := ⟨⟨u, huH⟩, Subgroup.mem_subgroupOf.2 huP⟩) (a₂ := 1)
    (by simpa using hmem)
  exact congrArg (fun t : ↥(P.subgroupOf H) => ((t : ↥H) : G)) h2

theorem Sit.cyclic_centBar (hs : Sit m p B M R d z H) : IsCyclic ↥(centBar p R H) := by
  have hbb := hs.hb
  haveI : Fact p.Prime := ⟨hbb.prime⟩
  obtain ⟨P, hPH, hPp, -, hPel, -, -, -, -, hcard, -, hRP, -⟩ := hs.R_facts
  by_contra hnc
  have hEp : IsPGroup p ↥(centBar p R H) := IsPGroup.to_le hbb.rsyl.2.1 inf_le_right
  obtain ⟨F, hFE, hFel, hFcard⟩ :=
    exists_elemAbelian_sq (by have := hbb.five_le; omega) hEp hnc
  have hcomm : ∀ f ∈ F, ∀ x ∈ P, f * x = x * f := fun f hf x hx =>
    hs.centBar_comm hPH hPp hRP (hFE hf) hx
  have hdis : F ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huF, huP⟩
    exact Subgroup.mem_bot.2 (hs.centBar_inf_P hPH hPp (hFE huF) huP)
  have hel := elemAbelian_sup hFel hPel hcomm
  have h1 := hbb.rk _ hel
  rw [card_sup_of_commute hcomm hdis, hFcard, hcard, ← pow_add, hs.m_eq_and_inner.1] at h1
  have := (Nat.pow_le_pow_iff_right hbb.prime.one_lt).1 h1
  omega


theorem Sit.d_outer (hs : Sit m p B M R d z H) :
    barAut p H ⟨d, hs.dN⟩ ∉ innerAut (barOf p H) ∧ orderOf (barAut p H ⟨d, hs.dN⟩) = p := by
  have hbb := hs.hb
  haveI : Fact p.Prime := ⟨hbb.prime⟩
  have hnin : barAut p H ⟨d, hs.dN⟩ ∉ innerAut (barOf p H) := by
    rintro ⟨kb, hkb⟩
    obtain ⟨⟨k, hkH⟩, rfl⟩ := QuotientGroup.mk_surjective kb
    apply hs.ninner
    refine ⟨k, hkH, ?_⟩
    have hkN : k ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hkH
    have hmem : k⁻¹ * d ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).mul_mem ((Subgroup.normalizer (H : Set G)).inv_mem hkN) hs.dN
    have hγ : barAut p H ⟨k⁻¹ * d, hmem⟩ = 1 := by
      have : (⟨k⁻¹ * d, hmem⟩ : ↥(Subgroup.normalizer (H : Set G))) =
          (⟨k, hkN⟩ : ↥(Subgroup.normalizer (H : Set G)))⁻¹ * ⟨d, hs.dN⟩ := rfl
      rw [this, map_mul, map_inv, barAut_of_mem hkH, ← hkb]
      exact inv_mul_cancel _
    exact ⟨⟨⟨k⁻¹ * d, hmem⟩, hγ, rfl⟩, Subgroup.mem_top _⟩
  refine ⟨hnin, orderOf_eq_prime ?_ ?_⟩
  · rw [← map_pow]
    have : (⟨d, hs.dN⟩ : ↥(Subgroup.normalizer (H : Set G))) ^ p = 1 := by
      apply Subtype.ext
      show d ^ p = 1
      have := pow_orderOf_eq_one d
      rwa [hbb.dord] at this
    rw [this, map_one]
  · intro h
    exact hnin (h ▸ Subgroup.one_mem _)

theorem Sit.fixed_card_le (hs : Sit m p B M R d z H) {F : Subgroup G} (hFH : F ≤ H)
    (hFp : IsPGroup p F) (hFd : ∀ f ∈ F, d * f = f * d) : Nat.card F ≤ p := by
  have hbb := hs.hb
  haveI : Fact p.Prime := ⟨hbb.prime⟩
  obtain ⟨-, -, -, -, hfix, -⟩ := hs.L2
  obtain ⟨hnin, hord⟩ := hs.d_outer
  have hSp : IsPGroup p ↥(barX p H F) :=
    (hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hFH).symm).map _
  have h1 := hfix _ hord hnin (barX p H F) hSp ?_
  · rwa [card_barX_eq hbb.prime hFp hFH] at h1
  · rintro _ ⟨⟨f, hfH⟩, hfF, rfl⟩
    have hf : f ∈ F := Subgroup.mem_subgroupOf.1 hfF
    show barAut p H ⟨d, hs.dN⟩ (QuotientGroup.mk ⟨f, hfH⟩) = QuotientGroup.mk ⟨f, hfH⟩
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
    congr 1
    apply Subtype.ext
    show d * f * d⁻¹ = f
    rw [mul_inv_eq_iff_eq_mul]
    exact hFd f hf

theorem Sit.torus (hs : Sit m p B M R d z H) {y : G} (hyH : y ∈ H) (hy1 : y ≠ 1) (hyp : y ^ p = 1) :
    ∃ n ∈ H, n ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) ∧
      n * y * n⁻¹ ≠ y := by
  have hbb := hs.hb
  haveI : Fact p.Prime := ⟨hbb.prime⟩
  obtain ⟨-, -, -, -, -, hT⟩ := hs.L2
  have hord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hSH : Subgroup.zpowers y ≤ H := (Subgroup.zpowers_le).2 hyH
  have hSp : IsPGroup p ↥(Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hScard : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hord]
  have hSbp : IsPGroup p ↥(barX p H (Subgroup.zpowers y)) :=
    (hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm).map _
  have hSbcard : Nat.card (barX p H (Subgroup.zpowers y)) = p := by
    rw [card_barX_eq hbb.prime hSp hSH, hScard]
  obtain ⟨nb, hnb, s, hs', hne⟩ := hT _ hSbp hSbcard
  have hnb' := normalizer_barX_le hbb.prime hSp hSH hnb
  obtain ⟨⟨n, hnH⟩, hnN, rfl⟩ := hnb'
  have hnN' : n ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
    Subgroup.mem_subgroupOf.1 hnN
  refine ⟨n, hnH, hnN', fun hcomm => hne ?_⟩
  obtain ⟨⟨s0, hs0H⟩, hs0, rfl⟩ := hs'
  have hs0' : s0 ∈ Subgroup.zpowers y := Subgroup.mem_subgroupOf.1 hs0
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs0'
  have hc : n * y ^ i * n⁻¹ = y ^ i := by
    have := map_zpow (MulAut.conj n) y i
    simp only [MulAut.conj_apply, hcomm] at this
    exact this
  show QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨n, hnH⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨y ^ i, hs0H⟩ *
    (QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨n, hnH⟩)⁻¹ = QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨y ^ i, hs0H⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hc

end SitLemmas

structure RIC (p : ℕ) (R I : Subgroup G) : Prop where
  RN : ∀ r ∈ R, r ∈ Subgroup.normalizer (I : Set G)
  eq : R = (R ⊓ I) ⊔ centBar p R I
  dis : (R ⊓ I) ⊓ centBar p R I = ⊥
  rk : CFSG.Open.pRank p (R ⊓ I) = 1

section RICLemmas

variable {p : ℕ} {R I : Subgroup G}

theorem RIC.RI_normal (hr : RIC p R I) : ∀ r ∈ R, ∀ x ∈ R ⊓ I, r * x * r⁻¹ ∈ R ⊓ I :=
  fun r hr' x hx => ⟨R.mul_mem (R.mul_mem hr' hx.1) (R.inv_mem hr'),
    (Subgroup.mem_normalizer_iff.1 (hr.RN r hr') x).1 hx.2⟩

theorem RIC.C_normal (hr : RIC p R I) :
    ∀ r ∈ R, ∀ c ∈ centBar p R I, r * c * r⁻¹ ∈ centBar p R I := by
  intro r hr' c hc
  obtain ⟨⟨n, hn, hnc⟩, hcR⟩ := hc
  have hn1 : barAut p I n = 1 := hn
  let ρ : ↥(Subgroup.normalizer (I : Set G)) := ⟨r, hr.RN r hr'⟩
  refine ⟨⟨ρ * n * ρ⁻¹, ?_, ?_⟩, R.mul_mem (R.mul_mem hr' hcR) (R.inv_mem hr')⟩
  · show barAut p I (ρ * n * ρ⁻¹) = 1
    rw [map_mul, map_mul, hn1, mul_one, map_inv, mul_inv_cancel]
  · show (ρ : G) * (n : G) * (ρ : G)⁻¹ = r * c * r⁻¹
    rw [show (n : G) = c from hnc]

theorem RIC.comm (hr : RIC p R I) : ∀ a ∈ R ⊓ I, ∀ c ∈ centBar p R I, a * c = c * a := by
  intro a ha c hc
  have hcR : c ∈ R := hc.2
  have h1 : a * c * a⁻¹ * c⁻¹ ∈ R ⊓ I ⊓ centBar p R I := by
    constructor
    · have := hr.RI_normal c hcR a⁻¹ ((R ⊓ I).inv_mem ha)
      have h2 := (R ⊓ I).mul_mem ha this
      simpa [mul_assoc] using h2
    · have := hr.C_normal a ha.1 c hc
      exact (centBar p R I).mul_mem this ((centBar p R I).inv_mem hc)
  rw [hr.dis, Subgroup.mem_bot] at h1
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)

theorem RIC.cyclic (hr : RIC p R I) [hp : Fact p.Prime] (hp2 : p ≠ 2) (hRp : IsPGroup p R) :
    IsCyclic ↥(R ⊓ I) := by
  by_contra hnc
  have hpI : IsPGroup p ↥(R ⊓ I) := IsPGroup.to_le hRp inf_le_left
  obtain ⟨F, hFE, hFel, hFcard⟩ := exists_elemAbelian_sq hp2 hpI hnc
  have := card_le_pow_pRank hFE hFel
  rw [hr.rk, hFcard] at this
  have h2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 this
  omega

theorem RIC.exists_w (hr : RIC p R I) [hp : Fact p.Prime] (hp2 : p ≠ 2) (hRp : IsPGroup p R) :
    ∃ w ∈ R ⊓ I, w ≠ 1 ∧ w ^ p = 1 ∧
      ∀ x ∈ R ⊓ I, x ^ p = 1 → x ∈ Subgroup.zpowers w := by
  have hcyc := hr.cyclic hp2 hRp
  obtain ⟨E, hEI, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (R ⊓ I)
  rw [hr.rk, pow_one] at hEcard
  have hE1 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    exact hp.out.ne_one hEcard.symm
  obtain ⟨⟨w, hwE⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwp : w ^ p = 1 := hEel.2 w hwE
  have hword : orderOf w = p := orderOf_eq_prime hwp hw1'
  refine ⟨w, hEI hwE, hw1', hwp, fun x hx hxp => ?_⟩
  letI : CommGroup ↥(R ⊓ I) := IsCyclic.commGroup
  have hcomm : ∀ a ∈ R ⊓ I, ∀ b ∈ R ⊓ I, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(R ⊓ I)) ⟨b, hb⟩)
  have hwI : w ∈ R ⊓ I := hEI hwE
  have hel : IsElemAbelian p (Subgroup.zpowers x ⊔ Subgroup.zpowers w) :=
    elemAbelian_sup (isElemAbelian_zpowers hxp) (isElemAbelian_zpowers hwp) fun a ha b hb => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow (hcomm x hx w hwI : Commute x w) i j).eq
  have hFle : Subgroup.zpowers x ⊔ Subgroup.zpowers w ≤ R ⊓ I :=
    sup_le ((Subgroup.zpowers_le).2 hx) ((Subgroup.zpowers_le).2 hwI)
  have h1 := card_le_pow_pRank hFle hel
  rw [hr.rk, pow_one] at h1
  have hzw : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, hword]
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_right : Subgroup.zpowers w ≤
    Subgroup.zpowers x ⊔ Subgroup.zpowers w) (by rw [hzw]; exact h1)
  have : x ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers w := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  rw [← heq] at this
  exact this


theorem RIC.R_le_normalizer_C (hr : RIC p R I) :
    R ≤ Subgroup.normalizer ((centBar p R I : Subgroup G) : Set G) := by
  intro r hr'
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => hr.C_normal r hr' c hc, fun hc => ?_⟩
  have := hr.C_normal r⁻¹ (R.inv_mem hr') _ hc
  simpa [mul_assoc] using this


theorem RIC.comm_RI (hr : RIC p R I) [Fact p.Prime] (hp2 : p ≠ 2) (hRp : IsPGroup p R) :
    ∀ a ∈ R ⊓ I, ∀ b ∈ R ⊓ I, a * b = b * a := by
  haveI := hr.cyclic hp2 hRp
  letI : CommGroup ↥(R ⊓ I) := IsCyclic.commGroup
  exact fun a ha b hb => congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(R ⊓ I)) ⟨b, hb⟩)

end RICLemmas


section SitRIC

variable {m p : ℕ} {B M R : Subgroup G} {d z : G} {H : Subgroup G}

theorem Sit.cent_le_C (hs : Sit m p B M R d z H) {I : Subgroup G} (hr : RIC p R I)
    {P : Subgroup G} (hPH : P ≤ H) (hPp : IsPGroup p P) (hPel : IsElemAbelian p P) (hPB : P ≤ B)
    (hPcard : Nat.card P = p ^ p) (hRP : R ≤ Subgroup.normalizer (P : Set G)) {y : G} (hy : y ∈ P)
    (hyc : ∀ r ∈ R, r * y = y * r) : y ∈ centBar p R I := by
  have hbb := hs.hb
  haveI hp : Fact p.Prime := ⟨hbb.prime⟩
  have hp2 : p ≠ 2 := by have := hbb.five_le; omega
  have hRp : IsPGroup p ↥R := hbb.rsyl.2.1
  have hcyc := hr.cyclic hp2 hRp
  have hCR : centBar p R I ≤ R := inf_le_right
  have hPR : P ≤ R := hPB.trans hbb.bR
  have hRIN : R ⊓ I ≤ Subgroup.normalizer ((centBar p R I : Subgroup G) : Set G) :=
    fun a ha => hr.R_le_normalizer_C ha.1
  have hPC : P ⊓ centBar p R I ≠ ⊥ := by
    intro hbot
    let C' : Subgroup ↥R := (centBar p R I).subgroupOf R
    haveI hC'n : C'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCR).2 hr.R_le_normalizer_C
    have hψ : Function.Injective
        ((QuotientGroup.mk' C').comp (Subgroup.inclusion hPR)) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (Subgroup.inclusion hPR x) ∈ C' := (QuotientGroup.eq_one_iff _).1 hx
      have hxC : (x : G) ∈ centBar p R I := Subgroup.mem_subgroupOf.1 hx'
      have : (x : G) ∈ P ⊓ centBar p R I := ⟨x.2, hxC⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have hφ : Function.Surjective
        ((QuotientGroup.mk' C').comp (Subgroup.inclusion (inf_le_left : R ⊓ I ≤ R))) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H r =>
        have hrmem : (r : G) ∈ (((R ⊓ I) ⊔ centBar p R I : Subgroup G) : Set G) := by
          rw [← hr.eq]
          exact r.2
        rw [Subgroup.coe_mul_of_left_le_normalizer_right (R ⊓ I) (centBar p R I) hRIN] at hrmem
        obtain ⟨a, ha, c, hc, hac⟩ := hrmem
        refine ⟨⟨a, ha⟩, ?_⟩
        show (QuotientGroup.mk (⟨a, ha.1⟩ : ↥R) : ↥R ⧸ C') = QuotientGroup.mk r
        rw [QuotientGroup.eq]
        refine Subgroup.mem_subgroupOf.2 ?_
        have : ((⟨a, ha.1⟩ : ↥R)⁻¹ * r : ↥R) = ⟨c, hCR hc⟩ := by
          apply Subtype.ext
          show a⁻¹ * (r : G) = c
          rw [← hac]
          group
        rw [this]
        exact hc
    haveI := hcyc
    haveI hPcyc : IsCyclic ↥P := by
      haveI := isCyclic_of_surjective _ hφ
      exact isCyclic_of_injective _ hψ
    have h1 : Nat.card P ∣ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => Subtype.ext (hPel.2 x.1 x.2))
    have h2 := Nat.le_of_dvd hp.out.pos h1
    rw [hPcard] at h2
    have h3 : p ^ 1 < p ^ p := Nat.pow_lt_pow_right hp.out.one_lt (by have := hbb.five_le; omega)
    rw [pow_one] at h3
    omega
  have hQN : R ≤ Subgroup.normalizer ((P ⊓ centBar p R I : Subgroup G) : Set G) := by
    intro r hr'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxP, hxC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 (hRP hr') x).1 hxP,
        (Subgroup.mem_normalizer_iff.1 (hr.R_le_normalizer_C hr') x).1 hxC⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 (hRP hr') x).2 h1,
        (Subgroup.mem_normalizer_iff.1 (hr.R_le_normalizer_C hr') x).2 h2⟩
  letI : MulDistribMulAction ↥R ↥(P ⊓ centBar p R I) := conjAction R (P ⊓ centBar p R I) hQN
  have hQp : IsPGroup p ↥(P ⊓ centBar p R I) := IsPGroup.to_le hPp inf_le_left
  have hdvd : p ∣ Nat.card ↥(P ⊓ centBar p R I) := by
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hk
      exact hPC hk
    rw [hk]
    exact dvd_pow_self p hk0
  obtain ⟨b, hbfix, hb1⟩ := hRp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (↥(P ⊓ centBar p R I)) hdvd (a := 1)
    (by rw [MulAction.mem_fixedPoints]; intro r; exact smul_one r)
  have hbcomm : ∀ r ∈ R, r * (b : G) * r⁻¹ = b := fun r hr' =>
    congrArg (fun t : ↥(P ⊓ centBar p R I) => (t : G)) (MulAction.mem_fixedPoints.1 hbfix ⟨r, hr'⟩)
  by_contra hyC
  have hbP : (b : G) ∈ P := b.2.1
  have hbC : (b : G) ∈ centBar p R I := b.2.2
  have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h.symm)
  have hyp : y ^ p = 1 := hPel.2 y hy
  have hbp : (b : G) ^ p = 1 := hPel.2 b hbP
  have hy1 : y ≠ 1 := fun h => hyC (h ▸ (centBar p R I).one_mem)
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hbord : orderOf (b : G) = p := orderOf_eq_prime hbp hb1'
  have hy_notin : y ∉ Subgroup.zpowers (b : G) := fun h => hyC ((Subgroup.zpowers_le).2 hbC h)
  have hdis : Subgroup.zpowers (b : G) ⊓ Subgroup.zpowers y = ⊥ := by
    have := inf_zpowers_eq_bot hyord hy_notin
    exact this
  have hcomm : ∀ a ∈ Subgroup.zpowers (b : G), ∀ c ∈ Subgroup.zpowers y, a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact (Commute.zpow_zpow (comm_of_mem hPel hbP hy : Commute (b : G) y) i j).eq
  have hFP : Subgroup.zpowers (b : G) ⊔ Subgroup.zpowers y ≤ P :=
    sup_le ((Subgroup.zpowers_le).2 hbP) ((Subgroup.zpowers_le).2 hy)
  have hFel : IsElemAbelian p (Subgroup.zpowers (b : G) ⊔ Subgroup.zpowers y) :=
    elemAbelian_sup (isElemAbelian_zpowers hbp) (isElemAbelian_zpowers hyp) hcomm
  have hbd : (b : G) ∈ Cg d := by
    have := hbcomm d hbb.dR
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hyd : y ∈ Cg d := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hyc d hbb.dR).symm
  have hFd : Subgroup.zpowers (b : G) ⊔ Subgroup.zpowers y ≤ Cg d :=
    sup_le ((Subgroup.zpowers_le).2 hbd) ((Subgroup.zpowers_le).2 hyd)
  have h2 := hs.fixed_card_le (hFP.trans hPH) (IsPGroup.to_le hPp hFP) (fun f hf =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hFd hf)).symm)
  rw [card_sup_of_commute hcomm hdis, Nat.card_zpowers, Nat.card_zpowers, hbord, hyord] at h2
  have := hp.out.two_le
  nlinarith


theorem Sit.iv (hs : Sit m p B M R d z H) {I : Subgroup G} (hr : RIC p R I)
    (hNR : ∀ y ∈ Subgroup.normalizer (R : Set G), y ∈ M)
    (hIM : ∀ g ∈ M, g ∈ Subgroup.normalizer (I : Set G)) :
    Subgroup.zpowers z = omegaOne p (R ⊓ I) := by
  have hbb := hs.hb
  haveI hp : Fact p.Prime := ⟨hbb.prime⟩
  have hp2 : p ≠ 2 := by have := hbb.five_le; omega
  have hRp : IsPGroup p ↥R := hbb.rsyl.2.1
  obtain ⟨w, hwRI, hw1, hwp, hwΩ⟩ := hr.exists_w hp2 hRp
  have hword : orderOf w = p := orderOf_eq_prime hwp hw1
  have hΩ : omegaOne p (R ⊓ I) = Subgroup.zpowers w := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨hx, hxp⟩
      exact hwΩ x hx hxp
    · exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure ⟨hwRI, hwp⟩)
  rw [hΩ]
  suffices hwz : w ∈ Subgroup.zpowers z by
    have hzw : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hbb.zo]
    have hww : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, hword]
    exact (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hwz) (by rw [hzw, hww])).symm
  by_contra hwz
  have hcommRI := hr.comm_RI hp2 hRp
  have hwcomm : ∀ r ∈ R, r * w = w * r := by
    intro r hr'
    have hRIN : R ⊓ I ≤ Subgroup.normalizer ((centBar p R I : Subgroup G) : Set G) :=
      fun a ha => hr.R_le_normalizer_C ha.1
    have hrmem : r ∈ (((R ⊓ I) ⊔ centBar p R I : Subgroup G) : Set G) := by
      rw [← hr.eq]
      exact hr'
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (R ⊓ I) (centBar p R I) hRIN] at hrmem
    obtain ⟨a, ha, c, hc, rfl⟩ := hrmem
    show a * c * w = w * (a * c)
    calc a * c * w = a * (c * w) := mul_assoc _ _ _
      _ = a * (w * c) := by rw [← hr.comm w hwRI c hc]
      _ = (a * w) * c := (mul_assoc _ _ _).symm
      _ = (w * a) * c := by rw [hcommRI a ha w hwRI]
      _ = w * (a * c) := mul_assoc _ _ _
  have hwZ : w ∈ centerOf R := Lemma1315.mem_centerOf_iff'.2 ⟨hwRI.1, hwcomm⟩
  have hwΩ1 : w ∈ omegaOne p (centerOf R) := Subgroup.subset_closure ⟨hwZ, hwp⟩
  have hwB : w ∈ B := l1110_omegaOne_centerOf_le hbb.bsc hbb.bR hwΩ1
  obtain ⟨P, hPH, hPp, hPmax, hPel, hPB, hBeq, hdis, hBH, hPcard, hRH, hRP, hRB⟩ := hs.R_facts
  have hPN : P ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := fun e he =>
    mem_normalizer_zpowers_of_commute (hs.H_comm_z e (hPH he) z (Subgroup.mem_zpowers z))
  have hwBm : w ∈ ((P ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := hBeq ▸ hwB
  rw [Subgroup.coe_mul_of_left_le_normalizer_right P (Subgroup.zpowers z) hPN] at hwBm
  obtain ⟨y, hy, zi, hzi, hwyz⟩ := hwBm
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hzi
  have hwyz' : y * z ^ i = w := hwyz
  have hyw : y = w * (z ^ i)⁻¹ := by rw [← hwyz']; group
  have hyc : ∀ r ∈ R, r * y = y * r := by
    intro r hr'
    have hc1 : Commute r w := hwcomm r hr'
    have hc2 : Commute r (z ^ i) := Commute.zpow_right (hbb.zR r hr' : Commute r z) i
    rw [hyw]
    exact (hc1.mul_right hc2.inv_right).eq
  have hy1 : y ≠ 1 := by
    intro h
    apply hwz
    rw [← hwyz', h, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i
  have hyC : y ∈ centBar p R I := hs.cent_le_C hr hPH hPp hPel hPB hPcard hRP hy hyc
  have hzi1 : z ^ i ≠ 1 := by
    intro h
    have hwy : w = y := by rw [← hwyz', h, mul_one]
    have : w ∈ (R ⊓ I) ⊓ centBar p R I := ⟨hwRI, hwy ▸ hyC⟩
    rw [hr.dis, Subgroup.mem_bot] at this
    exact hw1 this
  have hz1 : z ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hbb.zo] at this
  have hziord : orderOf (z ^ i) = p :=
    orderOf_eq_prime ((isElemAbelian_zpowers hz1).2 _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i)) hzi1
  have hyp : y ^ p = 1 := hPel.2 y hy
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  obtain ⟨n, hnH, hnN, hny⟩ := hs.torus (hPH hy) hy1 hyp
  have hy'mem : n * y * n⁻¹ ∈ Subgroup.zpowers y :=
    (Subgroup.mem_normalizer_iff.1 hnN y).1 (Subgroup.mem_zpowers y)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hy'mem
  have hnz : n * z ^ i * n⁻¹ = z ^ i := mul_inv_eq_iff_eq_mul.2
    (Commute.zpow_right (hs.H_comm_z n hnH z (Subgroup.mem_zpowers z) : Commute n z) i).eq
  have hg : n * w * n⁻¹ = (n * y * n⁻¹) * z ^ i := by
    rw [← hwyz']
    calc n * (y * z ^ i) * n⁻¹ = (n * y * n⁻¹) * (n * z ^ i * n⁻¹) := by group
      _ = (n * y * n⁻¹) * z ^ i := by rw [hnz]
  have hyZ : y ∈ centerOf R := Lemma1315.mem_centerOf_iff'.2 ⟨hbb.bR (hPB hy), hyc⟩
  have hzZ : z ∈ centerOf R := Lemma1315.mem_centerOf_iff'.2 ⟨hbb.bR hbb.zB, hbb.zR⟩
  have hgZ : n * w * n⁻¹ ∈ centerOf R := by
    rw [hg]
    exact (centerOf R).mul_mem ((Subgroup.zpowers_le).2 hyZ hy'mem)
      (Subgroup.zpow_mem _ hzZ i)
  obtain ⟨n', hn'N, hn'⟩ := sylow_fusion hbb.rsyl hwZ hgZ
  have hn'RI : n' * w * n'⁻¹ ∈ R ⊓ I :=
    ⟨(Subgroup.mem_normalizer_iff.1 hn'N w).1 hwRI.1,
      (Subgroup.mem_normalizer_iff.1 (hIM n' (hNR n' hn'N)) w).1 hwRI.2⟩
  have hn'p : (n' * w * n'⁻¹) ^ p = 1 := by
    have := map_pow (MulAut.conj n') w p
    simp only [MulAut.conj_apply, hwp, map_one] at this
    exact this.symm
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.1 (hwΩ _ hn'RI hn'p)
  have hyz : Commute y (z ^ i) := (Commute.zpow_right
    (hs.H_comm_z y (hPH hy) z (Subgroup.mem_zpowers z) : Commute y z) i)
  have hmain : y ^ a * z ^ i = y ^ c * (z ^ i) ^ c := by
    rw [ha, ← hg, ← hn', ← hc, ← hwyz']
    exact hyz.mul_zpow c
  have hyac : (y ^ c)⁻¹ * y ^ a = (z ^ i) ^ c * (z ^ i)⁻¹ := by
    have h1 : (y ^ c)⁻¹ * (y ^ a * z ^ i) = (z ^ i) ^ c := by
      rw [hmain]; group
    calc (y ^ c)⁻¹ * y ^ a = (y ^ c)⁻¹ * (y ^ a * z ^ i) * (z ^ i)⁻¹ := by group
      _ = (z ^ i) ^ c * (z ^ i)⁻¹ := by rw [h1]
  have hHz : H ⊓ Subgroup.zpowers z = ⊥ := inf_zpowers_eq_bot hbb.zo hs.z_not_mem
  have hboth : (y ^ c)⁻¹ * y ^ a ∈ H ⊓ Subgroup.zpowers z := by
    refine ⟨H.mul_mem (H.inv_mem (Subgroup.zpow_mem _ (hPH hy) c)) (Subgroup.zpow_mem _ (hPH hy) a), ?_⟩
    rw [hyac]
    exact (Subgroup.zpowers z).mul_mem
      (Subgroup.zpow_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i) c)
      ((Subgroup.zpowers z).inv_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i))
  rw [hHz, Subgroup.mem_bot] at hboth
  have hyac1 : y ^ a = y ^ c := (inv_mul_eq_one.1 hboth).symm
  have hzc1 : (z ^ i) ^ c = z ^ i := by
    have : (z ^ i) ^ c * (z ^ i)⁻¹ = 1 := by rw [← hyac]; exact hboth
    exact mul_inv_eq_one.1 this
  have hdvd : (orderOf (z ^ i) : ℤ) ∣ c - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub_one, hzc1]
    exact mul_inv_cancel _
  rw [hziord, ← hyord, orderOf_dvd_iff_zpow_eq_one, zpow_sub_one] at hdvd
  have hyc1 : y ^ c = y := mul_inv_eq_one.1 hdvd
  apply hny
  rw [← ha, hyac1, hyc1]

end SitRIC

end Structure




section Assembly

variable {G : Type} [Group G] [Finite G]

theorem normalizer_R_le_M {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsEkIn p 2 B U)
    (hUZ : U ≤ centerOf R) : ∀ y ∈ Subgroup.normalizer (R : Set G), y ∈ M := by
  have hβ : p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ m ≤ GLATwoLocalRank p G := h.standing.beta
  have hp : p.Prime := hβ.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBSC : IsSCp p ⊤ B := lemma23_proved G m p h.standing B h.bOne
  have hBR : B ≤ R := le_trans le_sup_right h.hR.2
  have hZB : omegaOne p (centerOf R) ≤ B := l1110_omegaOne_centerOf_le hBSC hBR
  have hUZ' : U ≤ omegaOne p (centerOf R) := fun u hu =>
    Subgroup.subset_closure ⟨hUZ hu, hU.2.1.2 u hu⟩
  have h2 : 2 ≤ CFSG.Open.pRank p (omegaOne p (centerOf R)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hUZ' hU.2.1 hU.2.2
  have hmemS : Subgroup.normalizer ((omegaOne p (centerOf R) : Subgroup G) : Set G) ∈
      {N : Subgroup G | ∃ Q : Subgroup G, Q ≤ B ∧ 2 ≤ CFSG.Open.pRank p Q ∧
        N = Subgroup.normalizer (Q : Set G)} :=
    ⟨omegaOne p (centerOf R), hZB, h2, rfl⟩
  have hNZ : Subgroup.normalizer ((omegaOne p (centerOf R) : Subgroup G) : Set G) ≤ M :=
    le_trans (le_sSup hmemS) h.uniq.clause_d
  intro y hy
  exact hNZ (Lemma1315.mem_normalizer_omegaOne hy)

theorem mem_normalizer_Iof {p : ℕ} {M D : Subgroup G} (h139a : Prop139a p M D) :
    ∀ g ∈ M, g ∈ Subgroup.normalizer ((Iof p M D : Subgroup G) : Set G) := by
  have hI : Iof p M D = Istar p M D := h139a.2.1
  have hle : ∀ g ∈ M, GLBConj g (Iof p M D) ≤ Iof p M D := fun g hg =>
    (le_iSup₂_of_le g hg le_rfl : GLBConj g (Iof p M D) ≤ Istar p M D).trans hI.symm.le
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => ?_, fun hx => hle g hg (mem_gLBConj.2 hx)⟩
  refine hle g⁻¹ (M.inv_mem hg) (mem_gLBConj.2 ?_)
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rw [e]
  exact hx

theorem A_data {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {z : G} (hb : Basic m p B M R d z) :
    IsSCp p (Cg z) A ∧ d ∈ A ∧ z ∈ A := by
  haveI : Fact p.Prime := ⟨hb.prime⟩
  have hA : IsSCp p ⊤ A :=
    (lemma104_ii_holds h.toSec13.toSec11.toSec10Fails h.toSec13.toSec11.pair).2
  have hAR : A ≤ R := le_trans le_sup_left h.hR.2
  have hAX : A ≤ Cg z := hAR.trans hb.R_le_Cg
  have hdA : d ∈ A := h.hD.1 h.hd.1
  have hz1 : z ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hb.zo] at this
  have hcomm : ∀ a ∈ A, ∀ c ∈ Subgroup.zpowers z, a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact (Commute.zpow_right (hb.zR a (hAR ha) : Commute a z) i).eq
  have hel := elemAbelian_sup hA.2.1 (isElemAbelian_zpowers hz1) hcomm
  have heq := hA.2.2 _ le_top hel le_sup_left
  have hzA : z ∈ A := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  exact ⟨⟨hAX, hA.2.1, fun E _ hEel hAE => hA.2.2 E le_top hEel hAE⟩, hdA, hzA⟩

theorem exists_sit {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h1314 : Lemma1314Statement) (hI : Inputs)
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) (hUR : U ≤ centerOf R) {z : G} {H0 : Subgroup G}
    (hz : z ∈ U ∧ z ≠ 1) (hH0 : GLAPComponent p (Cg2 d z) H0) (hH0M : ¬ H0 ≤ M)
    (hH0t : Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0))) :
    ∃ H : Subgroup G, H = (⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0) ∧
      TypeResult p (Cg z) H0 H d ∧ Sit m p B M R d z H := by
  have hb := basic_of_cex h h139a hU hUR hz
  have hstd := h.standing
  haveI : IsSimpleGroup G := hstd.simple
  have hX : Cg z ≠ ⊤ := centralizer_ne_top_of_simple hstd.nonabelian hz.2
  obtain ⟨hAsc, hdA, hzA⟩ := A_data h hb
  have h14 := h1314 h h139a
  have hAr : CFSG.Open.pRank p A = 3 := h14.2.2.2
  have tr := type_analysis hb hI hstd hX hH0 hH0M hH0t hAsc hAr hdA hzA
    (H := ⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0) rfl
  have hHM : ¬ (⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0) ≤ M := fun hle => hH0M (tr.H0H.trans hle)
  exact ⟨_, rfl, tr, hb, tr.comp, tr.dN, hb.B_le_normalizer hstd hI.i112 tr.comp,
    hb.centBar_B_eq hstd hI.i112 tr.comp hHM, tr.ninner, hI.iL2 p hb.prime hb.five_le _ tr.lq⟩

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem lemma1315_of_inputs (h1314 : Lemma1314Statement)
    (hI2319 : Lemma1315b.Input23_19) (hI255 : Lemma1315b.Input25_5) (hI33 : Lemma1315b.Input3_3)
    (hI144 : Lemma1315b.Input14_4_1) (hI1418 : Lemma1315b.Input14_18)
    (hI1415 : Lemma1314.Input14_15) (hFi23 : Lemma1314.Input23_24Fi23)
    (hI112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (hI183 : Prop115.Input18_3Gen) (hDiag : Lemma1315b.Input18_3DiagZ)
    (hL2 : Lemma1315b.InputL2) : Lemma1315Statement := by
  have hI : Lemma1315b.Inputs :=
    ⟨hI2319, hI255, hI33, hI144, hI1418, hI1415, hFi23, hI112, hI183, hDiag, hL2⟩
  intro G _ _ m p B M E A D T R L0 d h h139a U hU hUR z H0 hz hH0 hH0M hH0t H
  obtain ⟨H', hH', tr, hs⟩ := Lemma1315b.exists_sit h1314 hI h h139a hU hUR hz hH0 hH0M hH0t
  subst hH'
  have h14 := h1314 h h139a
  have hIM := Lemma1315b.mem_normalizer_Iof h139a
  have hr : Lemma1315b.RIC p R (Iof p M D) :=
    ⟨fun r hr' => hIM r (hs.hb.rM hr'), h14.1.1, h14.1.2.1, h14.1.2.2⟩
  obtain ⟨P, -, -, -, -, -, -, -, -, -, -, -, hRB⟩ := hs.R_facts
  exact ⟨⟨tr.p57, tr.lp, tr.lq, hs.cyclic_centBar, tr.dN, tr.ninner⟩,
    Lemma1315.sylow_of_central_rank_two h hU.1 hUR, hRB,
    hs.iv hr (Lemma1315b.normalizer_R_le_M h hU.1 hUR) hIM⟩

namespace Lemma1315b

@[expose] def ExtrasStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) (hUR : U ≤ centerOf R) {z : G} {H0 : Subgroup G}
    (hz : z ∈ U ∧ z ≠ 1) (hH0 : GLAPComponent p (Cg2 d z) H0) (hH0M : ¬ H0 ≤ M)
    (hH0t : Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0))),
    let H := ⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0
    IsSylowIn p H (B ⊓ H) ∧
      (B = (B ⊓ H) ⊔ Subgroup.zpowers z ∧ (B ⊓ H) ⊓ Subgroup.zpowers z = ⊥) ∧ R ⊓ H = B ⊓ H ∧
      (∀ x ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G),
        x ∈ Subgroup.normalizer (H : Set G)) ∧ m = p + 1

end Lemma1315b

theorem lemma1315_extras_of_inputs (h1314 : Lemma1314Statement)
    (hI2319 : Lemma1315b.Input23_19) (hI255 : Lemma1315b.Input25_5) (hI33 : Lemma1315b.Input3_3)
    (hI144 : Lemma1315b.Input14_4_1) (hI1418 : Lemma1315b.Input14_18)
    (hI1415 : Lemma1314.Input14_15) (hFi23 : Lemma1314.Input23_24Fi23)
    (hI112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (hI183 : Prop115.Input18_3Gen) (hDiag : Lemma1315b.Input18_3DiagZ)
    (hL2 : Lemma1315b.InputL2) : Lemma1315b.ExtrasStatement := by
  have hI : Lemma1315b.Inputs :=
    ⟨hI2319, hI255, hI33, hI144, hI1418, hI1415, hFi23, hI112, hI183, hDiag, hL2⟩
  intro G _ _ m p B M E A D T R L0 d h h139a U hU hUR z H0 hz hH0 hH0M hH0t H
  obtain ⟨H', hH', tr, hs⟩ := Lemma1315b.exists_sit h1314 hI h h139a hU hUR hz hH0 hH0M hH0t
  subst hH'
  obtain ⟨P, hPH, hPp, hPmax, -, hPB, hBeq, hdis, hBH, -, hRH, -, -⟩ := hs.R_facts
  have hBH' : B ⊓ H = P := hBH
  refine ⟨?_, ?_, ?_, fun x hx => hs.normalizer_zpowers_le hx, hs.m_eq_and_inner.1⟩
  · rw [hBH']
    exact ⟨hPH, hPp, hPmax⟩
  · rw [hBH']
    exact ⟨hBeq, hdis⟩
  · rw [hBH']
    exact hRH

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end

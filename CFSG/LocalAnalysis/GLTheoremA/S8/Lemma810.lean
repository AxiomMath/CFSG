module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp
public import CFSG.Monster.B.Short.Extraspecial
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace S8

namespace L89

variable {G : Type} [Group G] [Finite G]

abbrev cfgT (R M : Subgroup G) : Subgroup G := R ⊔ pCoreOf 2 M

section Generic

variable {p : ℕ}

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hBA : B ≤ Subgroup.normalizer (A : Set G)) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, mul_one y⟩
    · exact ⟨1, A.one_mem, y, hy, one_mul y⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := ihy
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := ihz
    refine ⟨a₁ * (b₁ * a₂ * b₁⁻¹), A.mul_mem ha₁ ((Subgroup.mem_normalizer_iff.1 (hBA hb₁) a₂).1 ha₂),
      b₁ * b₂, B.mul_mem hb₁ hb₂, by group⟩
  | inv y _ ihy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ihy
    refine ⟨b⁻¹ * a⁻¹ * b, ?_, b⁻¹, B.inv_mem hb, by group⟩
    have := (Subgroup.mem_normalizer_iff.1 (hBA (B.inv_mem hb)) a⁻¹).1 (A.inv_mem ha)
    simpa using this

theorem comm_mem_of_sup_left {A₁ A₂ Z : Subgroup G} {b : G}
    (hAZ : A₁ ⊔ A₂ ≤ Subgroup.centralizer (Z : Set G)) (h₁ : ∀ a ∈ A₁, ⁅a, b⁆ ∈ Z)
    (h₂ : ∀ a ∈ A₂, ⁅a, b⁆ ∈ Z) : ∀ a ∈ A₁ ⊔ A₂, ⁅a, b⁆ ∈ Z := by
  intro a ha
  have ha' := ha
  rw [Subgroup.sup_eq_closure] at ha'
  induction ha' using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact h₁ y hy
    · exact h₂ y hy
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hy' : y ∈ A₁ ⊔ A₂ := by rw [Subgroup.sup_eq_closure]; exact hy
    have hz' : z ∈ A₁ ⊔ A₂ := by rw [Subgroup.sup_eq_closure]; exact hz
    have hc : y * ⁅z, b⁆ * y⁻¹ = ⁅z, b⁆ := by
      have := Subgroup.mem_centralizer_iff.1 (hAZ hy') _ (ihz hz')
      rw [← this]
      group
    have e : ⁅y * z, b⁆ = (y * ⁅z, b⁆ * y⁻¹) * ⁅y, b⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hc]
    exact Z.mul_mem (ihz hz') (ihy hy')
  | inv y hy ihy =>
    have hy' : y ∈ A₁ ⊔ A₂ := by rw [Subgroup.sup_eq_closure]; exact hy
    have hc : y⁻¹ * ⁅y, b⁆⁻¹ * y = ⁅y, b⁆⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ (hAZ hy')) _ (Z.inv_mem (ihy hy'))
      calc y⁻¹ * ⁅y, b⁆⁻¹ * y = (y⁻¹ * ⁅y, b⁆⁻¹ * y⁻¹⁻¹) := by group
        _ = ⁅y, b⁆⁻¹ := by rw [← this]; group
    have e : ⁅y⁻¹, b⁆ = y⁻¹ * ⁅y, b⁆⁻¹ * y := by
      simp only [commutatorElement_def]
      group
    rw [e, hc]
    exact Z.inv_mem (ihy hy')

theorem comm_mem_of_sup_right {B₁ B₂ Z : Subgroup G} {a : G}
    (hBZ : B₁ ⊔ B₂ ≤ Subgroup.centralizer (Z : Set G)) (h₁ : ∀ b ∈ B₁, ⁅a, b⁆ ∈ Z)
    (h₂ : ∀ b ∈ B₂, ⁅a, b⁆ ∈ Z) : ∀ b ∈ B₁ ⊔ B₂, ⁅a, b⁆ ∈ Z := by
  intro b hb
  have key : ∀ b ∈ B₁ ⊔ B₂, ⁅b, a⁆ ∈ Z := comm_mem_of_sup_left hBZ
    (fun b hb => by rw [← commutatorElement_inv]; exact Z.inv_mem (h₁ b hb))
    (fun b hb => by rw [← commutatorElement_inv]; exact Z.inv_mem (h₂ b hb))
  rw [← commutatorElement_inv]
  exact Z.inv_mem (key b hb)

theorem es_basic {Q : Subgroup G} (hQ : IsExtraSpec2 Q ∨ Nat.card Q = 2) :
    IsPGroup 2 Q ∧ Nat.card (centerOf Q) = 2 ∧ ⁅Q, Q⁆ ≤ centerOf Q ∧
      (IsExtraSpec2 Q → ⁅Q, Q⁆ = centerOf Q) := by
  have hcQ : Nat.card (centerOf Q) = Nat.card (Subgroup.center ↥Q) := by
    unfold centerOf
    exact Subgroup.card_map_of_injective Q.subtype_injective
  have hcomm : ⁅Q, Q⁆ = (commutator ↥Q).map Q.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hes : IsExtraSpec2 Q → ⁅Q, Q⁆ = centerOf Q := by
    intro h
    rw [hcomm]
    unfold centerOf
    rw [h.2.1.trans h.2.2.1]
  rcases hQ with h | h
  · exact ⟨h.1, hcQ.trans h.2.2.2, (hes h).le, hes⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic ↥Q := isCyclic_of_prime_card h
    have hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
      intro a ha b hb
      have hc : (⟨a, ha⟩ : ↥Q) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
        (IsCyclic.commGroup (α := ↥Q)).mul_comm _ _
      have := congrArg Subtype.val hc
      simpa using this
    have hcen : centerOf Q = Q := by
      ext g
      rw [mem_centerOf_iff]
      exact ⟨fun hg => hg.1, fun hg => ⟨hg, fun k hk => hab k hk g hg⟩⟩
    refine ⟨IsPGroup.of_card (n := 1) (by rw [h, pow_one]), by rw [hcen, h], ?_, fun h' => hes h'⟩
    have hbot : ⁅Q, Q⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hab b hb a ha
    rw [hbot]
    exact bot_le

theorem center_le_centralizer {Q D : Subgroup G} (hZ : Nat.card (centerOf Q) = 2)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) : centerOf Q ≤ Subgroup.centralizer (D : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  obtain ⟨hzQ, hzc⟩ := mem_centerOf_iff.1 hz
  have hdz : d * z * d⁻¹ ∈ centerOf Q := by
    refine mem_centerOf_iff.2 ⟨(Subgroup.mem_normalizer_iff.1 (hDQ hd) z).1 hzQ, fun h hh => ?_⟩
    have hh' : d⁻¹ * h * d ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hDQ hd)) h).1 hh
      simpa using this
    have hc := hzc _ hh'
    calc h * (d * z * d⁻¹) = d * ((d⁻¹ * h * d) * z) * d⁻¹ := by group
      _ = d * (z * (d⁻¹ * h * d)) * d⁻¹ := by rw [hc]
      _ = d * z * d⁻¹ * h := by group
  by_cases hz1 : z = 1
  · subst hz1
    simp
  · have hne : d * z * d⁻¹ ≠ 1 := fun h => hz1 (by simpa using h)
    obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : ↥(centerOf Q))).1 hZ
    have h1 : (⟨d * z * d⁻¹, hdz⟩ : ↥(centerOf Q)) = ⟨z, hz⟩ := by
      rw [hw ⟨d * z * d⁻¹, hdz⟩ (fun h => hne (congrArg Subtype.val h)),
        hw ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))]
    have h2 : d * z * d⁻¹ = z := congrArg Subtype.val h1
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [h2]

theorem mem_center_iff_mem_centerOf {P : Subgroup G} (x : ↥P) :
    x ∈ Subgroup.center ↥P ↔ (x : G) ∈ centerOf P := by
  unfold centerOf
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy

theorem es_of_props {P : Subgroup G} (hP2 : IsPGroup 2 P) (hZ : Nat.card (centerOf P) = 2)
    (hcomm : ∀ g ∈ P, ∀ h ∈ P, ⁅g, h⁆ ∈ centerOf P) (hsq : ∀ g ∈ P, g ^ 2 ∈ centerOf P)
    (hna : ¬ P ≤ centerOf P) : IsExtraSpec2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : Nat.card (Subgroup.center ↥P) = 2 := by
    rw [← hZ]
    unfold centerOf
    exact (Subgroup.card_map_of_injective P.subtype_injective).symm
  have hcl : _root_.commutator ↥P ≤ Subgroup.center ↥P := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [mem_center_iff_mem_centerOf]
    have := hcomm a a.2 b b.2
    simpa [commutatorElement_def] using this
  haveI hcomm' : IsMulCommutative (↥P ⧸ Subgroup.center ↥P) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Subgroup.center ↥P)).2 hcl
  have hexp : Monoid.exponent (↥P ⧸ Subgroup.center ↥P) ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_iff_mem_centerOf]
      have := hsq x x.2
      simpa using this
  have hnt : Nontrivial (↥P ⧸ Subgroup.center ↥P) := by
    rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
    intro htop
    apply hna
    intro g hg
    have : (⟨g, hg⟩ : ↥P) ∈ Subgroup.center ↥P := htop ▸ Subgroup.mem_top _
    exact (mem_center_iff_mem_centerOf _).1 this
  haveI hE : CFSG.IsExtraspecial 2 ↥P :=
    { center_order_p := hcen
      quotient_elementary_abelian := { exponent_dvd_p := hexp }
      quotient_nontrivial := hnt }
  have h := CFSG.IsExtraspecial.isExtraspecialPGroup (p := 2) (P := ↥P)
  exact ⟨h.1, h.2.1.trans h.2.2.1.symm, h.2.2.1, h.2.2.2⟩

theorem es_sq {Q : Subgroup G} (hQ : IsExtraSpec2 Q) {g : G} (hg : g ∈ Q) : g ^ 2 ∈ centerOf Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥Q) := ⟨hQ.1⟩
  have h := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (⟨g, hg⟩ : ↥Q)
  rw [hQ.2.2.1] at h
  have := (mem_center_iff_mem_centerOf _).1 h
  simpa using this

theorem es_not_le_center {Q : Subgroup G} (hQ : IsExtraSpec2 Q) : ¬ Q ≤ centerOf Q := by
  intro h
  obtain ⟨-, hZ, -, hcomm⟩ := es_basic (Or.inl hQ)
  have hbot : ⁅Q, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (mem_centerOf_iff.1 (h ha)).2 b hb
  rw [hcomm hQ] at hbot
  rw [hbot, Subgroup.card_bot] at hZ
  norm_num at hZ

theorem comm_fix_commutator {Q D : Subgroup G} (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hQ : IsExtraSpec2 Q ∨ Nat.card Q = 2) :
    ⁅Q ⊓ Subgroup.centralizer (D : Set G), ⁅Q, D⁆⁆ = ⊥ := by
  obtain ⟨-, hZ2, hQQ, -⟩ := es_basic hQ
  have hZD := center_le_centralizer hZ2 hDQ
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_commutator_eq_bot_of_rotate
  · have h : ⁅D, Q ⊓ Subgroup.centralizer (D : Set G)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right
    rw [h, Subgroup.commutator_bot_left]
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact ((Subgroup.commutator_mono inf_le_left le_rfl).trans hQQ).trans hZD

theorem commutator_es (hp : p.Prime) (hp2 : p ≠ 2) {Q D : Subgroup G} (hD : IsPGroup p D)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsExtraSpec2 Q ∨ Nat.card Q = 2) :
    ⁅Q, D⁆ = ⊥ ∨ IsExtraSpec2 ⁅Q, D⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ2, hZ2, hQQ, -⟩ := es_basic hQ
  have hPQ : ⁅Q, D⁆ ≤ Q := commutator_le_of_le_normalizer hDQ
  have hP2 : IsPGroup 2 (⁅Q, D⁆ : Subgroup G) := hQ2.to_le hPQ
  by_cases hP1 : ⁅Q, D⁆ = ⊥
  · exact Or.inl hP1
  right
  have hdec := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_sup_centralizer_commutator hD hDQ
    (coprime_card_of_two hp hp2 hQ2)
  have hCP := comm_fix_commutator hDQ hQ
  have hPC : ⁅Q, D⁆ ≤ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hCP
    exact hCP
  have hZPQ : centerOf ⁅Q, D⁆ ≤ centerOf Q := by
    intro z hz
    obtain ⟨hzP, hzc⟩ := mem_centerOf_iff.1 hz
    refine mem_centerOf_iff.2 ⟨hPQ hzP, fun q hq => ?_⟩
    obtain ⟨c, hc, r, hr, rfl⟩ := exists_mul_of_mem_sup (le_normalizer_of_le_centralizer hPC) (hdec hq)
    have h1 : c * z = z * c := (Subgroup.mem_centralizer_iff.1 (hPC hzP) c hc)
    have h2 : r * z = z * r := hzc r hr
    calc c * r * z = c * (r * z) := by group
      _ = c * (z * r) := by rw [h2]
      _ = (c * z) * r := by group
      _ = (z * c) * r := by rw [h1]
      _ = z * (c * r) := by group
  have hZP : Nat.card (centerOf ⁅Q, D⁆) = 2 := by
    have hdvd := Subgroup.card_dvd_of_le hZPQ
    rw [hZ2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exfalso
      haveI : Nontrivial ↥(⁅Q, D⁆ : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).2 hP1
      haveI := hP2.center_nontrivial
      have hcard : Nat.card (Subgroup.center ↥(⁅Q, D⁆ : Subgroup G)) = 1 := by
        rw [← h]
        unfold centerOf
        exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
      rw [Nat.card_eq_one_iff_unique] at hcard
      exact not_subsingleton _ hcard.1
    · exact h
  have hZeq : centerOf ⁅Q, D⁆ = centerOf Q := Subgroup.eq_of_le_of_card_ge hZPQ (by rw [hZ2, hZP])
  have hZD : centerOf Q ≤ Subgroup.centralizer (D : Set G) := center_le_centralizer hZ2 hDQ
  have hPD : ⁅Q, D⁆ ≤ ⁅⁅Q, D⁆, D⁆ := by
    have hcop : Nat.Coprime (Nat.card D) (Nat.card Q) := by
      obtain ⟨k, hk⟩ := hD.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_left k (coprime_card_of_two hp hp2 hQ2)
    have hsolv : Group.IsSolvable ↥Q := by
      haveI := hQ2.isNilpotent
      infer_instance
    rw [GL83.commutator_double_eq_self D Q hDQ hcop hsolv]
  have hna : ¬ ⁅Q, D⁆ ≤ centerOf ⁅Q, D⁆ := by
    intro hab
    have h0 : ⁅⁅Q, D⁆, D⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hab.trans (hZeq ▸ hZD)
    exact hP1 (le_bot_iff.1 (h0 ▸ hPD))
  have hQes : IsExtraSpec2 Q := by
    rcases hQ with h | h
    · exact h
    · exfalso
      apply hna
      have hQZ : centerOf Q = Q :=
        Subgroup.eq_of_le_of_card_ge (fun z hz => (mem_centerOf_iff.1 hz).1) (by rw [h, hZ2])
      intro g hg
      refine mem_centerOf_iff.2 ⟨hg, fun h' hh' => ?_⟩
      have hgZ : g ∈ centerOf Q := hQZ.symm ▸ hPQ hg
      exact (mem_centerOf_iff.1 hgZ).2 h' (hPQ hh')
  refine es_of_props hP2 hZP (fun g hg h hh => ?_) (fun g hg => ?_) hna
  · rw [hZeq]
    exact hQQ (Subgroup.commutator_mem_commutator (hPQ hg) (hPQ hh))
  · rw [hZeq]
    exact es_sq hQes (hPQ hg)

theorem comm_sup_fix {V R0 D : Subgroup G} (hVR : V ≤ Subgroup.centralizer (R0 : Set G))
    (hRD : R0 ≤ Subgroup.centralizer (D : Set G)) (hDV : D ≤ Subgroup.normalizer (V : Set G))
    (hV : V ≤ ⁅V, D⁆) : ⁅V ⊔ R0, D⁆ = V := by
  apply le_antisymm _ (hV.trans (Subgroup.commutator_mono le_sup_left le_rfl))
  have hRV : R0 ≤ Subgroup.normalizer (V : Set G) := by
    apply le_normalizer_of_le_centralizer
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 (hVR hv) r hr).symm
  rw [Subgroup.commutator_le]
  intro u hu d hd
  obtain ⟨v, hv, r, hr, rfl⟩ := exists_mul_of_mem_sup hRV hu
  have hrd : r * d = d * r := (Subgroup.mem_centralizer_iff.1 (hRD hr) d hd).symm
  have h1 : r * d * r⁻¹ = d := by rw [hrd]; group
  have h2 : ⁅v * r, d⁆ = ⁅v, d⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc v * r * d * (v * r)⁻¹ * d⁻¹ = v * (r * d * r⁻¹) * v⁻¹ * d⁻¹ := by group
      _ = v * d * v⁻¹ * d⁻¹ := by rw [h1]
  rw [h2]
  exact commutator_le_of_le_normalizer hDV (Subgroup.commutator_mem_commutator hv hd)

theorem le_pCore_of_stabilizes (hchar : IsCharTwoType G) {M A : Subgroup G} (hM : IsTwoLocal M)
    (hAM : A ≤ M) (h1 : ⁅A, pCoreOf 2 M⁆ ≤ ⁅pCoreOf 2 M, pCoreOf 2 M⁆)
    (h2 : ⁅A, ⁅pCoreOf 2 M, pCoreOf 2 M⁆⁆ = ⊥) : A ≤ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := pCoreOf 2 M with hS
  set S' := ⁅S, S⁆ with hS'
  have hMS : M ≤ Subgroup.normalizer (S : Set G) := le_normalizer_pCoreOf 2 M
  have hMS' : M ≤ Subgroup.normalizer (S' : Set G) := le_normalizer_commutator' hMS hMS
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  let St : Subgroup G :=
    { carrier := {m | m ∈ M ∧ (∀ s ∈ S, ⁅m, s⁆ ∈ S') ∧ ∀ s ∈ S', ⁅m, s⁆ = 1}
      one_mem' := ⟨M.one_mem, fun s _ => by simp, fun s _ => by simp⟩
      mul_mem' := by
        rintro m m' ⟨hm, hm1, hm2⟩ ⟨hm', hm1', hm2'⟩
        have e : ∀ s, ⁅m * m', s⁆ = (m * ⁅m', s⁆ * m⁻¹) * ⁅m, s⁆ := fun s => by
          simp only [commutatorElement_def]
          group
        refine ⟨M.mul_mem hm hm', fun s hs => ?_, fun s hs => ?_⟩
        · rw [e]
          exact S'.mul_mem ((Subgroup.mem_normalizer_iff.1 (hMS' hm) _).1 (hm1' s hs)) (hm1 s hs)
        · rw [e, hm2' s hs, hm2 s hs]
          group
      inv_mem' := by
        rintro m ⟨hm, hm1, hm2⟩
        have e : ∀ s, ⁅m⁻¹, s⁆ = m⁻¹ * ⁅m, s⁆⁻¹ * m⁻¹⁻¹ := fun s => by
          simp only [commutatorElement_def]
          group
        refine ⟨M.inv_mem hm, fun s hs => ?_, fun s hs => ?_⟩
        · rw [e]
          exact (Subgroup.mem_normalizer_iff.1 (hMS' (M.inv_mem hm)) _).1 (S'.inv_mem (hm1 s hs))
        · rw [e, hm2 s hs]
          group }
  have hSt : ∀ m, m ∈ St ↔ m ∈ M ∧ (∀ s ∈ S, ⁅m, s⁆ ∈ S') ∧ ∀ s ∈ S', ⁅m, s⁆ = 1 :=
    fun m => Iff.rfl
  have hASt : A ≤ St := by
    intro a ha
    refine (hSt a).2 ⟨hAM ha, fun s hs => h1 (Subgroup.commutator_mem_commutator ha hs), fun s hs => ?_⟩
    have := Subgroup.commutator_mem_commutator ha hs
    rw [h2] at this
    exact Subgroup.mem_bot.1 this
  have hStM : St ≤ M := fun m hm => ((hSt m).1 hm).1
  have hMSt : M ≤ Subgroup.normalizer (St : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_le
    intro m hm
    obtain ⟨hm, hm1, hm2⟩ := (hSt m).1 hm
    have hgS : ∀ s ∈ S, g⁻¹ * s * g ∈ S := fun s hs => by
      have := (Subgroup.mem_normalizer_iff.1 (hMS (M.inv_mem hg)) s).1 hs
      simpa using this
    have hgS' : ∀ s ∈ S', g⁻¹ * s * g ∈ S' := fun s hs => by
      have := (Subgroup.mem_normalizer_iff.1 (hMS' (M.inv_mem hg)) s).1 hs
      simpa using this
    have e : ∀ s, ⁅g * m * g⁻¹, s⁆ = g * ⁅m, g⁻¹ * s * g⁆ * g⁻¹ := fun s => by
      simp only [commutatorElement_def]
      group
    refine (hSt _).2 ⟨M.mul_mem (M.mul_mem hg hm) (M.inv_mem hg), fun s hs => ?_, fun s hs => ?_⟩
    · rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hMS' hg) _).1 (hm1 _ (hgS s hs))
    · rw [e, hm2 _ (hgS' s hs)]
      group
  have key : ∀ h ∈ St, Odd (orderOf h) → h = 1 := by
    intro h hh hodd
    obtain ⟨hhM, -, -⟩ := (hSt h).1 hh
    have hPS : Subgroup.zpowers h ≤ Subgroup.normalizer (S : Set G) := (Subgroup.zpowers_le).2 (hMS hhM)
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers h)) (Nat.card S) := by
      rw [Nat.card_zpowers]
      obtain ⟨n, hn⟩ := hS2.exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
    have hsolv : Group.IsSolvable ↥S := by
      haveI := hS2.isNilpotent
      infer_instance
    have hdbl := GL83.commutator_double_eq_self (Subgroup.zpowers h) S hPS hcop hsolv
    have hSP : ⁅S, Subgroup.zpowers h⁆ ≤ S' := by
      rw [Subgroup.commutator_le]
      intro s hs q hq
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      have := ((hSt _).1 (St.zpow_mem hh j)).2.1 s hs
      rw [← commutatorElement_inv]
      exact S'.inv_mem this
    have hS'P : ⁅S', Subgroup.zpowers h⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro s hs q hq
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      have := ((hSt _).1 (St.zpow_mem hh j)).2.2 s hs
      rw [← commutatorElement_inv, this, inv_one]
      exact Subgroup.one_mem _
    have hbot : ⁅S, Subgroup.zpowers h⁆ = ⊥ := by
      rw [← hdbl]
      exact le_bot_iff.1 ((Subgroup.commutator_mono hSP le_rfl).trans hS'P.le)
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    have hhS : h ∈ S := hchar M hM ⟨hhM, hbot (Subgroup.mem_zpowers h)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨h, hhS⟩
    have h2n : orderOf h = 2 ^ n := by
      rw [← hn]
      exact Subgroup.orderOf_coe (⟨h, hhS⟩ : ↥S)
    rw [h2n] at hodd
    have hn0 : n = 0 := by
      by_contra hn0
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hn0⟩)
    rw [hn0, pow_zero] at h2n
    exact orderOf_eq_one_iff.1 h2n
  have hSt2 : IsPGroup 2 St := by
    intro x
    obtain ⟨k, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hy : orderOf (x ^ (2 ^ k)) = r := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hord ▸ dvd_mul_right _ _), hord]
      exact Nat.mul_div_cancel_left r (pow_pos two_pos k)
    refine ⟨k, Subtype.ext ?_⟩
    have := key _ (x ^ (2 ^ k)).2 (by rw [Subgroup.orderOf_coe, hy]; exact hr)
    simpa using this
  exact hASt.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hStM hMSt hSt2)

theorem conj_mem_centralizer {U : Subgroup G} {b s : G} (hb : b ∈ Subgroup.normalizer (U : Set G))
    (hs : s ∈ Subgroup.centralizer (U : Set G)) : b * s * b⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hs ⊢
  intro u hu
  have hu' : b⁻¹ * u * b ∈ U := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) u).1 hu
    simpa using this
  have h := hs _ hu'
  calc u * (b * s * b⁻¹) = b * ((b⁻¹ * u * b) * s) * b⁻¹ := by group
    _ = b * (s * (b⁻¹ * u * b)) * b⁻¹ := by rw [h]
    _ = b * s * b⁻¹ * u := by group

theorem exists_U2 {T U : Subgroup G} (hT2 : IsPGroup 2 T) (hUT : U ≤ T)
    (hgen : T ≤ U ⊔ (T ⊓ Subgroup.centralizer (U : Set G))) (hne : U ≠ T) :
    ∃ U2 : Subgroup G, U2 ≤ T ⊓ Subgroup.centralizer (U : Set G) ∧ ¬ U2 ≤ U ∧
      ⁅T ⊓ Subgroup.centralizer (U : Set G), U2⁆ ≤ U ∧
      ∀ B : Subgroup G, B ≤ Subgroup.normalizer (T : Set G) → B ≤ Subgroup.normalizer (U : Set G) →
        B ≤ Subgroup.normalizer (U2 : Set G) := by
  set U₁ := T ⊓ Subgroup.centralizer (U : Set G) with hU₁
  have hcomU : ∀ s ∈ U₁, ∀ u ∈ U, s * u * s⁻¹ = u := by
    intro s hs u hu
    have h := Subgroup.mem_centralizer_iff.1 hs.2 u hu
    calc s * u * s⁻¹ = u * s * s⁻¹ := by rw [h]
      _ = u := by group
  let U₂ : Subgroup G :=
    { carrier := {t | t ∈ U₁ ∧ ∀ s ∈ U₁, ⁅t, s⁆ ∈ U}
      one_mem' := ⟨U₁.one_mem, fun s _ => by simp⟩
      mul_mem' := by
        rintro t t' ⟨ht, hts⟩ ⟨ht', hts'⟩
        refine ⟨U₁.mul_mem ht ht', fun s hs => ?_⟩
        have e : ⁅t * t', s⁆ = (t * ⁅t', s⁆ * t⁻¹) * ⁅t, s⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, hcomU t ht _ (hts' s hs)]
        exact U.mul_mem (hts' s hs) (hts s hs)
      inv_mem' := by
        rintro t ⟨ht, hts⟩
        refine ⟨U₁.inv_mem ht, fun s hs => ?_⟩
        have e : ⁅t⁻¹, s⁆ = t⁻¹ * ⁅t, s⁆⁻¹ * t⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e, hcomU t⁻¹ (U₁.inv_mem ht) _ (U.inv_mem (hts s hs))]
        exact U.inv_mem (hts s hs) }
  have hU₂ : ∀ t, t ∈ U₂ ↔ t ∈ U₁ ∧ ∀ s ∈ U₁, ⁅t, s⁆ ∈ U := fun t => Iff.rfl
  refine ⟨U₂, fun t ht => ((hU₂ t).1 ht).1, ?_, ?_, ?_⟩
  · intro hle
    have hU₁U : ¬ U₁ ≤ U := fun h => hne (le_antisymm hUT (hgen.trans (sup_le le_rfl h)))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let N : Subgroup ↥U₁ := U.subgroupOf U₁
    have hNn : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have : ((g * n * g⁻¹ : ↥U₁) : G) = (n : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hcomU g g.2 n hn
      rw [this]
      exact hn
    have hQ2 : IsPGroup 2 (↥U₁ ⧸ N) := (hT2.to_le inf_le_left).to_quotient N
    have hQnt : Nontrivial (↥U₁ ⧸ N) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      intro htop
      apply hU₁U
      intro s hs
      have : (⟨s, hs⟩ : ↥U₁) ∈ N := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    have hZnt := hQ2.center_nontrivial
    obtain ⟨q, hq⟩ := exists_ne (1 : Subgroup.center (↥U₁ ⧸ N))
    obtain ⟨⟨t, ht⟩, hqt⟩ := QuotientGroup.mk_surjective (q : ↥U₁ ⧸ N)
    have htU₂ : t ∈ U₂ := by
      refine (hU₂ t).2 ⟨ht, fun s hs => ?_⟩
      have hc := Subgroup.mem_center_iff.1 q.2 (QuotientGroup.mk ⟨s, hs⟩)
      rw [← hqt] at hc
      have h1 : (QuotientGroup.mk (⁅(⟨t, ht⟩ : ↥U₁), ⟨s, hs⟩⁆) : ↥U₁ ⧸ N) = 1 := by
        rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hc]
        group
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      simpa [commutatorElement_def] using h1
    have htU : t ∉ U := by
      intro htU
      apply hq
      apply Subtype.ext
      rw [← hqt]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 htU)
    exact htU (hle htU₂)
  · rw [Subgroup.commutator_le]
    intro s hs t ht
    rw [← commutatorElement_inv]
    exact U.inv_mem (((hU₂ t).1 ht).2 s hs)
  · intro B hBT hBU b hb
    have hbU₁ : ∀ g ∈ B, ∀ s ∈ U₁, g * s * g⁻¹ ∈ U₁ := fun g hg s hs =>
      ⟨(Subgroup.mem_normalizer_iff.1 (hBT hg) s).1 hs.1, conj_mem_centralizer (hBU hg) hs.2⟩
    apply mem_normalizer_of_conj_le
    intro t ht
    obtain ⟨ht1, hts⟩ := (hU₂ t).1 ht
    refine (hU₂ _).2 ⟨hbU₁ b hb t ht1, fun s hs => ?_⟩
    have hs' : b⁻¹ * s * b ∈ U₁ := by
      have := hbU₁ b⁻¹ (B.inv_mem hb) s hs
      simpa using this
    have e : ⁅b * t * b⁻¹, s⁆ = b * ⁅t, b⁻¹ * s * b⁆ * b⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hBU hb) _).1 (hts _ hs')

theorem exists_ne_one_of_hyperplane (hp : p.Prime) {A D : Subgroup G} (hDcard : Nat.card D = p ^ 2)
    (hA : (A.subgroupOf D).index = p) : ∃ a ∈ A, a ≠ 1 := by
  by_contra h
  push Not at h
  have hA0 : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
  rw [hA0, Subgroup.bot_subgroupOf, Subgroup.index_bot, hDcard] at hA
  have : p ^ 2 = p ^ 1 := by rw [pow_one]; exact hA
  have := Nat.pow_right_injective hp.two_le this
  omega

theorem exists_a_W (hp : p.Prime) (hp2 : p ≠ 2) {D U U2 : Subgroup G} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hU2 : IsPGroup 2 U2) (hU : IsPGroup 2 U)
    (hDU2 : D ≤ Subgroup.normalizer (U2 : Set G)) (hDU : D ≤ Subgroup.normalizer (U : Set G))
    (hcomm : ⁅U2, U2⁆ ≤ U) (hfix : U2 ⊓ Subgroup.centralizer (D : Set G) ≤ U) (hne : ¬ U2 ≤ U) :
    ∃ a ∈ D, a ≠ 1 ∧ ¬ ⁅U2 ⊓ cx a, D⁆ ≤ U := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  apply hne
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hN : ∀ t ∈ U2, ∀ x ∈ U ⊓ U2, t * x * t⁻¹ ∈ U ⊓ U2 := by
    intro t ht x hx
    have e : t * x * t⁻¹ = ⁅t, x⁆ * x := by
      rw [commutatorElement_def]
      group
    refine ⟨?_, U2.mul_mem (U2.mul_mem ht hx.2) (U2.inv_mem ht)⟩
    rw [e]
    exact U.mul_mem (hcomm (Subgroup.commutator_mem_commutator ht hx.2)) hx.1
  have hcU2 : ∀ u ∈ U2, ∀ d ∈ D, ⁅u, d⁆ ∈ U2 := by
    intro u hu d hd
    rw [commutatorElement_def]
    have h1 : d * u⁻¹ * d⁻¹ ∈ U2 := (Subgroup.mem_normalizer_iff.1 (hDU2 hd) _).1 (U2.inv_mem hu)
    have e : u * d * u⁻¹ * d⁻¹ = u * (d * u⁻¹ * d⁻¹) := by group
    rw [e]
    exact U2.mul_mem hu h1
  let F : Subgroup G :=
    { carrier := {u | u ∈ U2 ∧ ∀ d ∈ D, ⁅u, d⁆ ∈ U ⊓ U2}
      one_mem' := ⟨U2.one_mem, fun d _ => by simp⟩
      mul_mem' := by
        rintro u v ⟨hu, hud⟩ ⟨hv, hvd⟩
        refine ⟨U2.mul_mem hu hv, fun d hd => ?_⟩
        have e : ⁅u * v, d⁆ = (u * ⁅v, d⁆ * u⁻¹) * ⁅u, d⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (U ⊓ U2).mul_mem (hN u hu _ (hvd d hd)) (hud d hd)
      inv_mem' := by
        rintro u ⟨hu, hud⟩
        refine ⟨U2.inv_mem hu, fun d hd => ?_⟩
        have e : ⁅u⁻¹, d⁆ = u⁻¹ * ⁅u, d⁆⁻¹ * u⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hN u⁻¹ (U2.inv_mem hu) _ ((U ⊓ U2).inv_mem (hud d hd)) }
  have hF : ∀ u, u ∈ F ↔ u ∈ U2 ∧ ∀ d ∈ D, ⁅u, d⁆ ∈ U ⊓ U2 := fun u => Iff.rfl
  have hU2F : U2 ≤ F := by
    refine (GL83.le_iSup_hyperplane hp hp2 hDne hD hU2 hDU2).trans (iSup₂_le fun A hA => ?_)
    obtain ⟨a, haA, ha1⟩ := exists_ne_one_of_hyperplane hp hDcard hA.2
    intro g hg
    have hga : g ∈ U2 ⊓ cx a := ⟨hg.1, Subgroup.centralizer_le (Set.singleton_subset_iff.2 haA) hg.2⟩
    refine (hF g).2 ⟨hg.1, fun d hd => ⟨hcon a (hA.1 haA) ha1
      (Subgroup.commutator_mem_commutator hga hd), hcU2 g hg.1 d hd⟩⟩
  have hcomm2 : ⁅U2, D⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro u hu d hd
    exact (((hF u).1 (hU2F hu)).2 d hd).1
  exact (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_sup_centralizer_commutator
    (isPGroup_of_isElemAbelian hD) hDU2 (coprime_card_of_two hp hp2 hU2)).trans (sup_le hfix hcomm2)

theorem central_product_es {U W : Subgroup G} (hWU : W ≤ Subgroup.centralizer (U : Set G))
    (hU : IsExtraSpec2 U ∨ Nat.card U = 2) (hW : IsExtraSpec2 W) (hZW : centerOf W ≤ U) :
    IsExtraSpec2 (U ⊔ W) ∧ centerOf (U ⊔ W) = centerOf U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hU2, hZU, hUU, -⟩ := es_basic hU
  obtain ⟨hW2, hZW2, hWW, -⟩ := es_basic (Or.inl hW)
  have hcomm : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u := fun u hu w hw =>
    Subgroup.mem_centralizer_iff.1 (hWU hw) u hu
  have hZWU : centerOf W ≤ centerOf U := fun z hz =>
    mem_centerOf_iff.2 ⟨hZW hz, fun u hu => hcomm u hu z (mem_centerOf_iff.1 hz).1⟩
  have hZeq : centerOf W = centerOf U := Subgroup.eq_of_le_of_card_ge hZWU (by rw [hZU, hZW2])
  have hWnU : W ≤ Subgroup.normalizer (U : Set G) := le_normalizer_of_le_centralizer hWU
  have hZV : centerOf (U ⊔ W) = centerOf U := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxV, hxc⟩ := mem_centerOf_iff.1 hx
      obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup hWnU hxV
      have hu' : u ∈ centerOf U := by
        refine mem_centerOf_iff.2 ⟨hu, fun u' hu' => ?_⟩
        have h1 := hxc u' (Subgroup.mem_sup_left hu')
        have h2 : w * u' = u' * w := (hcomm u' hu' w hw).symm
        have h3 : u' * u * w = u * u' * w := by
          calc u' * u * w = u' * (u * w) := by group
            _ = (u * w) * u' := h1
            _ = u * (w * u') := by group
            _ = u * (u' * w) := by rw [h2]
            _ = u * u' * w := by group
        exact mul_right_cancel h3
      have hw' : w ∈ centerOf W := by
        refine mem_centerOf_iff.2 ⟨hw, fun w' hw' => ?_⟩
        have h1 := hxc w' (Subgroup.mem_sup_right hw')
        have h2 : u * w' = w' * u := hcomm u hu w' hw'
        have h3 : u * (w' * w) = u * (w * w') := by
          calc u * (w' * w) = (u * w') * w := by group
            _ = (w' * u) * w := by rw [h2]
            _ = w' * (u * w) := by group
            _ = (u * w) * w' := h1
            _ = u * (w * w') := by group
        exact mul_left_cancel h3
      rw [hZeq] at hw'
      exact (centerOf U).mul_mem hu' hw'
    · intro z hz
      have hzW : z ∈ centerOf W := hZeq.symm ▸ hz
      obtain ⟨hzU, hzc⟩ := mem_centerOf_iff.1 hz
      refine mem_centerOf_iff.2 ⟨Subgroup.mem_sup_left hzU, fun v hv => ?_⟩
      have hle : U ⊔ W ≤ cx z := by
        apply sup_le
        · intro u hu
          exact Subgroup.mem_centralizer_singleton_iff.2 (hzc u hu)
        · intro w hw
          exact Subgroup.mem_centralizer_singleton_iff.2 ((mem_centerOf_iff.1 hzW).2 w hw)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hv)
  have hVZ : U ⊔ W ≤ Subgroup.centralizer (centerOf U : Set G) := by
    rw [← hZV]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_centerOf_iff.1 hz).2 v hv).symm
  have hUW1 : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ = 1 := fun u hu w hw =>
    (commutatorElement_eq_one_iff_mul_comm).2 (hcomm u hu w hw)
  have hWU1 : ∀ w ∈ W, ∀ u ∈ U, ⁅w, u⁆ = 1 := fun w hw u hu =>
    (commutatorElement_eq_one_iff_mul_comm).2 (hcomm u hu w hw).symm
  refine ⟨es_of_props (IsPGroup.to_sup_of_normal_left' hU2 hW2 hWnU) (by rw [hZV]; exact hZU)
    (fun g hg h hh => ?_) (fun g hg => ?_) ?_, hZV⟩
  · rw [hZV]
    refine comm_mem_of_sup_left hVZ (fun u hu => ?_) (fun w hw => ?_) g hg
    · refine comm_mem_of_sup_right hVZ (fun u' hu' => hUU (Subgroup.commutator_mem_commutator hu hu'))
        (fun w hw => ?_) h hh
      rw [hUW1 u hu w hw]
      exact Subgroup.one_mem _
    · refine comm_mem_of_sup_right hVZ (fun u hu => ?_)
        (fun w' hw' => hZeq ▸ hWW (Subgroup.commutator_mem_commutator hw hw')) h hh
      rw [hWU1 w hw u hu]
      exact Subgroup.one_mem _
  · rw [hZV]
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup hWnU hg
    have hc : Commute u w := hcomm u hu w hw
    rw [hc.mul_pow]
    refine (centerOf U).mul_mem ?_ (hZeq ▸ es_sq hW hw)
    rcases hU with hU' | hU'
    · exact es_sq hU' hu
    · have h1 : orderOf u ∣ 2 := hU' ▸ Subgroup.orderOf_dvd_natCard U hu
      rw [orderOf_dvd_iff_pow_eq_one.1 h1]
      exact Subgroup.one_mem _
  · intro hle
    apply es_not_le_center hW
    intro w hw
    have h1 := hle (Subgroup.mem_sup_right hw)
    rw [hZV, ← hZeq] at h1
    exact h1

theorem i312 {T V : Subgroup G} (hVT : V ≤ T) (hV : IsExtraSpec2 V) (hTV : ⁅T, V⁆ ≤ centerOf V) :
    T ≤ V ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hE : CFSG.IsExtraspecial 2 ↥V :=
    (CFSG.isExtraspecialPGroup_iff_isExtraspecial).1 ⟨hV.1, hV.2.1.trans hV.2.2.1, hV.2.2.1, hV.2.2.2⟩
  intro t ht
  have htN : t ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_of_conj_le fun v hv => by
    have h1 : ⁅t, v⁆ ∈ V := (mem_centerOf_iff.1 (hTV (Subgroup.commutator_mem_commutator ht hv))).1
    have e : t * v * t⁻¹ = ⁅t, v⁆ * v := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem h1 hv
  let α : MulAut ↥V := V.normalizerMonoidHom ⟨t, htN⟩
  have hα : ∀ y : ↥V, ((α y : ↥V) : G) = t * y * t⁻¹ := fun y => rfl
  have hker : α ∈ (CFSG.SectionRank.Ccomm.autQuotient (frattini ↥V)).ker := by
    rw [CFSG.SectionRank.Ccomm.mem_ker_autQuotient]
    intro y
    rw [hV.2.2.1, mem_center_iff_mem_centerOf]
    have hc : ⁅t, (y : G)⁆ ∈ centerOf V := hTV (Subgroup.commutator_mem_commutator ht y.2)
    have hcomm := (mem_centerOf_iff.1 hc).2 y y.2
    have e : ((y⁻¹ * α y : ↥V) : G) = ⁅t, (y : G)⁆ := by
      show (y : G)⁻¹ * ((α y : ↥V) : G) = _
      rw [hα]
      calc (y : G)⁻¹ * (t * y * t⁻¹) = (y : G)⁻¹ * (⁅t, (y : G)⁆ * y) := by
            rw [commutatorElement_def]
            group
        _ = (y : G)⁻¹ * (y * ⁅t, (y : G)⁆) := by rw [hcomm]
        _ = ⁅t, (y : G)⁆ := by group
    rw [e]
    exact hc
  rw [← CFSG.Quasithin.range_conj_eq_ker_autQuotient_frattini (p := 2)] at hker
  obtain ⟨d, hd⟩ := hker
  have h2 : ∀ y ∈ V, (d : G) * y * (d : G)⁻¹ = t * y * t⁻¹ := by
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨y, hy⟩ : ↥V) : G)) hd
    simpa [MulAut.conj_apply, hα] using h1
  have hdt : (d : G)⁻¹ * t ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨T.mul_mem (T.inv_mem (hVT d.2)) ht, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    calc y * ((d : G)⁻¹ * t) = (d : G)⁻¹ * ((d : G) * y * (d : G)⁻¹) * t := by group
      _ = (d : G)⁻¹ * (t * y * t⁻¹) * t := by rw [h2 y hy]
      _ = (d : G)⁻¹ * t * y := by group
  have e : t = (d : G) * ((d : G)⁻¹ * t) := by group
  rw [e]
  exact Subgroup.mul_mem_sup d.2 hdt

theorem comm_T_V {T U W : Subgroup G} (hUT : U ≤ T)
    (hgen : T ≤ U ⊔ (T ⊓ Subgroup.centralizer (U : Set G)))
    (hW : W ≤ T ⊓ Subgroup.centralizer (U : Set G))
    (hU1W : ⁅T ⊓ Subgroup.centralizer (U : Set G), W⁆ ≤ U) (hUU : ⁅U, U⁆ ≤ centerOf U)
    (hZ : centerOf (U ⊔ W) = centerOf U) : ⁅T, U ⊔ W⁆ ≤ centerOf (U ⊔ W) := by
  rw [hZ]
  set U₁ := T ⊓ Subgroup.centralizer (U : Set G) with hU₁
  have hZU : centerOf U ≤ U := fun z hz => (mem_centerOf_iff.1 hz).1
  have hcen : ∀ z ∈ centerOf U, ∀ u ∈ U, u * z = z * u := fun z hz => (mem_centerOf_iff.1 hz).2
  have hUZ : U ≤ Subgroup.centralizer (centerOf U : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hcen z hz u hu).symm
  have hU₁Z : U₁ ≤ Subgroup.centralizer (centerOf U : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 hs.2 z (hZU hz))
  have hVZ : U ⊔ W ≤ Subgroup.centralizer (centerOf U : Set G) := by
    rw [← hZ]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_centerOf_iff.1 hz).2 v hv).symm
  have hU₁W : ⁅U₁, W⁆ ≤ centerOf U := by
    rw [centerOf_eq_inf]
    refine le_inf hU1W ?_
    rw [Subgroup.commutator_le]
    intro s hs w hw
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs.2 (hW hw).2)
      (Subgroup.inv_mem _ hs.2)) (Subgroup.inv_mem _ (hW hw).2)
  have hWU : ∀ w ∈ W, ∀ u ∈ U, ⁅u, w⁆ = 1 := by
    intro w hw u hu
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 (hW hw).2 u hu)
  rw [Subgroup.commutator_le]
  intro t ht v hv
  refine comm_mem_of_sup_left (sup_le hUZ hU₁Z) (fun u hu => ?_) (fun s hs => ?_) t (hgen ht)
  · refine comm_mem_of_sup_right hVZ (fun u' hu' => hUU (Subgroup.commutator_mem_commutator hu hu'))
      (fun w hw => ?_) v hv
    rw [hWU w hw u hu]
    exact Subgroup.one_mem _
  · refine comm_mem_of_sup_right hVZ (fun u' hu' => ?_)
      (fun w hw => hU₁W (Subgroup.commutator_mem_commutator hs hw)) v hv
    have : ⁅s, u'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.1 hs.2 u' hu').symm
    rw [this]
    exact Subgroup.one_mem _

end Generic

section Setup

variable {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem cfg_D_ne_bot (hp : p.Prime) (c : SporCfg G p x L row) : c.D ≠ ⊥ := by
  intro h
  have hc := c.hD.2.2.1
  rw [h, Subgroup.card_bot] at hc
  have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  omega

theorem le_comm_comm_D (hp : p.Prime) (hp2 : p ≠ 2) (c : SporCfg G p x L row) {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hDQ : c.D ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅Q, c.D⁆ ≤ ⁅⁅Q, c.D⁆, c.D⁆ := by
  have hcop : Nat.Coprime (Nat.card c.D) (Nat.card Q) := by
    rw [c.hD.2.2.1]
    exact Nat.Coprime.pow_left 2 (coprime_card_of_two hp hp2 hQ2)
  have hsolv : Group.IsSolvable ↥Q := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := hQ2.isNilpotent
    infer_instance
  rw [GL83.commutator_double_eq_self c.D Q hDQ hcop hsolv]

theorem cfg_R_le_M (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) : c.R ≤ M :=
  Subgroup.le_normalizer.trans hNM

theorem cfg_KB_le_M (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) : cfgK p x L c.D c.R ⊔ c.Bs ≤ M :=
  (cfg_KB_le_normalizer_R c).trans hNM

theorem T_isPGroup (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) : IsPGroup 2 (cfgT c.R M) ∧ cfgT c.R M ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 c.R := (es_basic (Or.inl c.hR.1)).1
  refine ⟨IsPGroup.to_sup_of_normal_right' hR2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    ((cfg_R_le_M c hNM).trans (le_normalizer_pCoreOf 2 M)), sup_le (cfg_R_le_M c hNM)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M)⟩

theorem KB_le_normalizer_T (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) :
    cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (cfgT c.R M : Set G) :=
  le_normalizer_sup' (cfg_KB_le_normalizer_R c) ((cfg_KB_le_M c hNM).trans (le_normalizer_pCoreOf 2 M))

theorem KB_le_normalizer_T_inf (c : SporCfg G p x L row) {M H : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M)
    (hH : cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (H : Set G)) :
    cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer ((cfgT c.R M ⊓ H : Subgroup G) : Set G) :=
  le_normalizer_inf' (KB_le_normalizer_T c hNM) hH

theorem T_inf_centralizer_D (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) :
    cfgT c.R M ⊓ Subgroup.centralizer (c.D : Set G) = cfgR0 c.R c.D := by
  obtain ⟨hT2, -⟩ := T_isPGroup c hNM
  apply le_antisymm _ (inf_le_inf_right _ le_sup_left)
  have hCD : cfgK p x L c.D c.R ⊔ c.Bs ≤
      Subgroup.normalizer ((Subgroup.centralizer (c.D : Set G) : Subgroup G) : Set G) :=
    (cfg_KB_le_centralizer_D c).trans Subgroup.le_normalizer
  have hle : c.R ⊔ (cfgT c.R M ⊓ Subgroup.centralizer (c.D : Set G)) ≤ cfgT c.R M :=
    sup_le le_sup_left inf_le_left
  have heq := c.hMax.2.2.2 (c.R ⊔ (cfgT c.R M ⊓ Subgroup.centralizer (c.D : Set G)))
    (sup_le c.hMax.1 (inf_le_right.trans (cfg_centralizer_D_le_cx c))) (hT2.to_le hle)
    (le_normalizer_sup' (cfg_KB_le_normalizer_R c) (KB_le_normalizer_T_inf c hNM hCD)) le_sup_left
  intro t ht
  refine ⟨?_, ht.2⟩
  rw [← heq]
  exact Subgroup.mem_sup_right ht

theorem T_inf_cx (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) : cfgT c.R M ⊓ cx x = c.R := by
  obtain ⟨hT2, -⟩ := T_isPGroup c hNM
  have hCx : cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer ((cx x : Subgroup G) : Set G) :=
    (cfg_KB_le_cx c).trans Subgroup.le_normalizer
  exact c.hMax.2.2.2 _ inf_le_right (hT2.to_le inf_le_left) (KB_le_normalizer_T_inf c hNM hCx)
    (le_inf le_sup_left c.hMax.1)

theorem Ta_inf_centralizer_D (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) {a : G} (ha : a ∈ c.D) :
    cfgT c.R M ⊓ cx a ⊓ Subgroup.centralizer (c.D : Set G) = cfgR0 c.R c.D := by
  rw [inf_assoc, inf_eq_right.2 (centralizer_le_cx_of_mem ha), T_inf_centralizer_D c hNM]

theorem KB_le_cx_of_mem (c : SporCfg G p x L row) {a : G} (ha : a ∈ c.D) :
    cfgK p x L c.D c.R ⊔ c.Bs ≤ cx a :=
  (cfg_KB_le_centralizer_D c).trans (centralizer_le_cx_of_mem ha)

theorem KB_le_normalizer_Ta (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) {a : G} (ha : a ∈ c.D) :
    cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer ((cfgT c.R M ⊓ cx a : Subgroup G) : Set G) :=
  KB_le_normalizer_T_inf c hNM ((KB_le_cx_of_mem c ha).trans Subgroup.le_normalizer)

theorem D_le_KB (c : SporCfg G p x L row) : c.D ≤ cfgK p x L c.D c.R ⊔ c.Bs :=
  (cfg_D_le_Bs c).trans le_sup_right

theorem KB_le_normalizer_D (c : SporCfg G p x L row) :
    cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (c.D : Set G) :=
  (cfg_KB_le_centralizer_D c).trans (Subgroup.centralizer_le_normalizer _)

end Setup

section Para1

variable {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem U_es (hc : S8Ctx G p) (hin : Inputs89 G p) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hrow : RowL row p L) (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1)
    {U : Subgroup G} (hUT : U ≤ cfgT c.R M ⊓ cx a) (hR0U : cfgR0 c.R c.D ≤ U)
    (hUn : cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (U : Set G)) :
    IsExtraSpec2 U ∨ Nat.card U = 2 := by
  by_cases hU : U = cfgR0 c.R c.D
  · rw [hU]; exact c.hR0
  left
  obtain ⟨hT2, -⟩ := T_isPGroup c hNM
  have hU2 : IsPGroup 2 U := hT2.to_le (hUT.trans inf_le_left)
  have hUD : ¬ U ≤ Subgroup.centralizer (c.D : Set G) := by
    intro h
    apply hU
    apply le_antisymm _ hR0U
    rw [← T_inf_centralizer_D c hNM]
    exact le_inf (hUT.trans inf_le_left) h
  have hiso := lemma89 hc hin hx hL hrow c ha ha1 (hUT.trans inf_le_right) hU2 hUn hUD
  obtain ⟨hJ, -, hIJ⟩ := ja_setup hc hin.i183 hin.i112s hin.i112r hin.i112n hin.cfgI hx hL hrow c ha ha1
  exact lemma88iii hc hin.i301B hin.cfgI hx hL hrow c ha ha1 hJ hiso hIJ (hUT.trans inf_le_right) hU2 hUn
    (lt_of_le_of_ne hR0U (Ne.symm hU))

theorem Ta_es (hc : S8Ctx G p) (hin : Inputs89 G p) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hrow : RowL row p L) (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) :
    IsExtraSpec2 (cfgT c.R M ⊓ cx a) ∨ Nat.card (cfgT c.R M ⊓ cx a : Subgroup G) = 2 := by
  refine U_es hc hin hx hL hrow c hNM ha ha1 le_rfl ?_ (KB_le_normalizer_Ta c hNM ha)
  rw [← Ta_inf_centralizer_D c hNM ha]
  exact inf_le_left

theorem Tsa_le_centralizer_R0 (hc : S8Ctx G p) (hin : Inputs89 G p) (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) :
    ⁅cfgT c.R M ⊓ cx a, c.D⁆ ≤ Subgroup.centralizer (cfgR0 c.R c.D : Set G) := by
  have h := comm_fix_commutator ((D_le_KB c).trans (KB_le_normalizer_Ta c hNM ha))
    (Ta_es hc hin hx hL hrow c hNM ha ha1)
  rw [Ta_inf_centralizer_D c hNM ha, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact (Subgroup.mem_centralizer_iff.1 (h hr) t ht).symm

theorem V_es (hc : S8Ctx G p) (hin : Inputs89 G p) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hrow : RowL row p L) (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1)
    {V : Subgroup G} (hVT : V ≤ ⁅cfgT c.R M ⊓ cx a, c.D⁆)
    (hVn : cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (V : Set G)) (hVD : V ≤ ⁅V, c.D⁆)
    (hV1 : V ≠ ⊥) : IsExtraSpec2 V := by
  have hp := hc.ctx.prime
  have hTaD : c.D ≤ Subgroup.normalizer ((cfgT c.R M ⊓ cx a : Subgroup G) : Set G) :=
    (D_le_KB c).trans (KB_le_normalizer_Ta c hNM ha)
  have hTsTa : ⁅cfgT c.R M ⊓ cx a, c.D⁆ ≤ cfgT c.R M ⊓ cx a := commutator_le_of_le_normalizer hTaD
  have hVR : V ≤ Subgroup.centralizer (cfgR0 c.R c.D : Set G) :=
    hVT.trans (Tsa_le_centralizer_R0 hc hin hx hL hrow c hNM ha ha1)
  have hR0Ta : cfgR0 c.R c.D ≤ cfgT c.R M ⊓ cx a := by
    rw [← Ta_inf_centralizer_D c hNM ha]; exact inf_le_left
  have hUes := U_es hc hin hx hL hrow c hNM ha ha1 (sup_le (hVT.trans hTsTa) hR0Ta) le_sup_right
    (le_normalizer_sup' hVn (cfg_KB_le_normalizer_R0 c))
  have hDU : c.D ≤ Subgroup.normalizer ((V ⊔ cfgR0 c.R c.D : Subgroup G) : Set G) :=
    (D_le_KB c).trans (le_normalizer_sup' hVn (cfg_KB_le_normalizer_R0 c))
  have heq : ⁅V ⊔ cfgR0 c.R c.D, c.D⁆ = V :=
    comm_sup_fix hVR (cfg_R0_le_centralizer c) ((D_le_KB c).trans hVn) hVD
  rcases commutator_es hp hc.ctx.odd (isPGroup_of_isElemAbelian c.hD.2.1) hDU hUes with h | h
  · exact absurd (heq ▸ h) hV1
  · rwa [heq] at h

end Para1

section Para2

variable {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem S_eq_T (hc : S8Ctx G p) (hin : Inputs89 G p) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hrow : RowL row p L) (c : SporCfg G p x L row) {M : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) (hT : IsExtraSpec2 (cfgT c.R M)) :
    pCoreOf 2 M = cfgT c.R M := by
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hD2, hD3, -⟩ := c.hD
  have hST : pCoreOf 2 M ≤ cfgT c.R M := le_sup_right
  have hKBM := cfg_KB_le_M c hNM
  have hDM : c.D ≤ M := (D_le_KB c).trans hKBM
  have hS2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hDS : c.D ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := hDM.trans (le_normalizer_pCoreOf 2 M)
  have hDnc : ¬ IsCyclic c.D := S3.not_isCyclic_of_card hp hD2 hD3.ge
  obtain ⟨-, h2⟩ := GL83.I_33_1_proved G hc.ctx.charTwo p hp hp2 c.D (pCoreOf 2 M) (cfg_D_ne_bot hp c) hD2
    hS2 hDS (Or.inr (Or.inl ⟨M, hM.1, hDM, rfl⟩))
  obtain ⟨-, a, -, ha, -, ha1, -, hSa, -⟩ := h2 c.D (cfg_D_ne_bot hp c) le_rfl hDnc
  rw [Subgroup.commutator_comm] at hSa
  have hDSa : c.D ≤ Subgroup.normalizer ((pCoreOf 2 M ⊓ cx a : Subgroup G) : Set G) :=
    le_normalizer_inf' hDS ((cfg_D_le_centralizer_D c).trans
      ((centralizer_le_cx_of_mem ha).trans Subgroup.le_normalizer))
  have hSsaS : ⁅pCoreOf 2 M ⊓ cx a, c.D⁆ ≤ pCoreOf 2 M :=
    (commutator_le_of_le_normalizer hDSa).trans inf_le_left
  have hSsaT : ⁅pCoreOf 2 M ⊓ cx a, c.D⁆ ≤ ⁅cfgT c.R M ⊓ cx a, c.D⁆ :=
    Subgroup.commutator_mono (inf_le_inf_right _ hST) le_rfl
  have hSsan : cfgK p x L c.D c.R ⊔ c.Bs ≤
      Subgroup.normalizer ((⁅pCoreOf 2 M ⊓ cx a, c.D⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' (le_normalizer_inf' (hKBM.trans (le_normalizer_pCoreOf 2 M))
      ((KB_le_cx_of_mem c ha).trans Subgroup.le_normalizer)) (KB_le_normalizer_D c)
  have hSsaD := le_comm_comm_D hp hp2 c (hS2.to_le inf_le_left) hDSa
  have hSes := V_es hc hin hx hL hrow c hNM ha ha1 hSsaT hSsan hSsaD hSa
  obtain ⟨-, hZ2, -, hcomm⟩ := es_basic (Or.inl hSes)
  have hS1 : ⁅pCoreOf 2 M, pCoreOf 2 M⁆ ≠ ⊥ := by
    intro h
    have hle : ⁅⁅pCoreOf 2 M ⊓ cx a, c.D⁆, ⁅pCoreOf 2 M ⊓ cx a, c.D⁆⁆ ≤ ⊥ :=
      h ▸ Subgroup.commutator_mono hSsaS hSsaS
    rw [hcomm hSes, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hZ2
    norm_num at hZ2
  obtain ⟨-, hTZ, -, hTcomm⟩ := es_basic (Or.inl hT)
  have hSST : ⁅pCoreOf 2 M, pCoreOf 2 M⁆ = ⁅cfgT c.R M, cfgT c.R M⁆ := by
    have hle : ⁅pCoreOf 2 M, pCoreOf 2 M⁆ ≤ ⁅cfgT c.R M, cfgT c.R M⁆ := Subgroup.commutator_mono hST hST
    rw [hTcomm hT] at hle ⊢
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hTZ] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hS1
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h, hTZ])
  have h1 : ⁅cfgT c.R M, pCoreOf 2 M⁆ ≤ ⁅pCoreOf 2 M, pCoreOf 2 M⁆ := by
    rw [hSST]
    exact Subgroup.commutator_mono le_rfl hST
  have h2' : ⁅cfgT c.R M, ⁅pCoreOf 2 M, pCoreOf 2 M⁆⁆ = ⊥ := by
    rw [hSST, hTcomm hT, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
      centerOf_eq_inf]
    exact inf_le_right
  exact le_antisymm hST (le_pCore_of_stabilizes hc.ctx.charTwo hM.1 (T_isPGroup c hNM).2 h1 h2')

end Para2

section Para3

variable {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

@[expose] def GoodU (T R0 A U : Subgroup G) : Prop :=
  U ≤ T ∧ (IsExtraSpec2 U ∨ Nat.card U = 2) ∧ T ≤ U ⊔ (T ⊓ Subgroup.centralizer (U : Set G)) ∧
    A ≤ Subgroup.normalizer (U : Set G) ∧ R0 ≤ U

theorem T_le_R0_cen (hc : S8Ctx G p) (hin : Inputs89 G p) (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) :
    cfgT c.R M ≤ cfgR0 c.R c.D ⊔ (cfgT c.R M ⊓ Subgroup.centralizer (cfgR0 c.R c.D : Set G)) := by
  have hp := hc.ctx.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hT2, -⟩ := T_isPGroup c hNM
  obtain ⟨-, hD2, hD3, -⟩ := c.hD
  have hDT : c.D ≤ Subgroup.normalizer (cfgT c.R M : Set G) := (D_le_KB c).trans (KB_le_normalizer_T c hNM)
  refine (GL83.le_iSup_hyperplane hp hc.ctx.odd (cfg_D_ne_bot hp c) hD2 hT2 hDT).trans
    (iSup₂_le fun A hA => ?_)
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    have hA0 : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    have hi := hA.2
    rw [hA0, Subgroup.bot_subgroupOf, Subgroup.index_bot, hD3] at hi
    have : p ^ 2 = p ^ 1 := by rw [pow_one]; exact hi
    have := Nat.pow_right_injective hp.two_le this
    omega
  have haD : a ∈ c.D := hA.1 haA
  refine (inf_le_inf_left _ (centralizer_le_cx_of_mem haA)).trans ?_
  have hDTa : c.D ≤ Subgroup.normalizer ((cfgT c.R M ⊓ cx a : Subgroup G) : Set G) :=
    (D_le_KB c).trans (KB_le_normalizer_Ta c hNM haD)
  have hdec := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_sup_centralizer_commutator
    (isPGroup_of_isElemAbelian hD2) hDTa (coprime_card_of_two hp hc.ctx.odd (hT2.to_le inf_le_left))
  rw [Ta_inf_centralizer_D c hNM haD] at hdec
  refine hdec.trans (sup_le le_sup_left (le_sup_of_le_right (le_inf ?_ ?_)))
  · exact (commutator_le_of_le_normalizer hDTa).trans inf_le_left
  · exact Tsa_le_centralizer_R0 hc hin hx hL hrow c hNM haD ha1

theorem goodU_step (hc : S8Ctx G p) (hin : Inputs89 G p) (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) {U : Subgroup G}
    (hU : GoodU (cfgT c.R M) (cfgR0 c.R c.D) (cfgK p x L c.D c.R ⊔ c.Bs) U) (hne : U ≠ cfgT c.R M) :
    ∃ V : Subgroup G, GoodU (cfgT c.R M) (cfgR0 c.R c.D) (cfgK p x L c.D c.R ⊔ c.Bs) V ∧
      Nat.card U < Nat.card V := by
  obtain ⟨hUT, hUes, hgen, hAU, hR0U⟩ := hU
  have hp := hc.ctx.prime
  obtain ⟨hT2, -⟩ := T_isPGroup c hNM
  obtain ⟨-, hD2, hD3, -⟩ := c.hD
  have hAT := KB_le_normalizer_T c hNM
  obtain ⟨U2, hU2, hU2U, hU2c, hU2n⟩ := exists_U2 hT2 hUT hgen hne
  have hAU2 := hU2n _ hAT hAU
  have hDU2 : c.D ≤ Subgroup.normalizer (U2 : Set G) := (D_le_KB c).trans hAU2
  have hDU : c.D ≤ Subgroup.normalizer (U : Set G) := (D_le_KB c).trans hAU
  have hU2T : U2 ≤ cfgT c.R M := hU2.trans inf_le_left
  have hcomm : ⁅U2, U2⁆ ≤ U := (Subgroup.commutator_mono hU2 le_rfl).trans hU2c
  have hfix : U2 ⊓ Subgroup.centralizer (c.D : Set G) ≤ U := by
    refine (inf_le_inf_right _ hU2T).trans ?_
    rw [T_inf_centralizer_D c hNM]
    exact hR0U
  obtain ⟨a, ha, ha1, haW⟩ := exists_a_W hp hc.ctx.odd hD2 hD3 (hT2.to_le hU2T) (hT2.to_le hUT) hDU2 hDU
    hcomm hfix hU2U
  have hDU2a : c.D ≤ Subgroup.normalizer ((U2 ⊓ cx a : Subgroup G) : Set G) :=
    le_normalizer_inf' hDU2 ((cfg_D_le_centralizer_D c).trans
      ((centralizer_le_cx_of_mem ha).trans Subgroup.le_normalizer))
  have hWle : ⁅U2 ⊓ cx a, c.D⁆ ≤ U2 ⊓ cx a := commutator_le_of_le_normalizer hDU2a
  have hWT' : ⁅U2 ⊓ cx a, c.D⁆ ≤ cfgT c.R M := hWle.trans (inf_le_left.trans hU2T)
  have hWT : ⁅U2 ⊓ cx a, c.D⁆ ≤ ⁅cfgT c.R M ⊓ cx a, c.D⁆ :=
    Subgroup.commutator_mono (inf_le_inf_right _ hU2T) le_rfl
  have hWn : cfgK p x L c.D c.R ⊔ c.Bs ≤
      Subgroup.normalizer ((⁅U2 ⊓ cx a, c.D⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' (le_normalizer_inf' hAU2 ((KB_le_cx_of_mem c ha).trans Subgroup.le_normalizer))
      (KB_le_normalizer_D c)
  have hWD := le_comm_comm_D hp hc.ctx.odd c (hT2.to_le (inf_le_left.trans hU2T)) hDU2a
  have hW1 : ⁅U2 ⊓ cx a, c.D⁆ ≠ ⊥ := fun h => haW (h ▸ bot_le)
  have hWes := V_es hc hin hx hL hrow c hNM ha ha1 hWT hWn hWD hW1
  have hWU : ⁅U2 ⊓ cx a, c.D⁆ ≤ Subgroup.centralizer (U : Set G) :=
    hWle.trans (inf_le_left.trans (hU2.trans inf_le_right))
  have hZW : centerOf ⁅U2 ⊓ cx a, c.D⁆ ≤ U := by
    have h1 := center_le_centralizer (es_basic (Or.inl hWes)).2.1 ((D_le_KB c).trans hWn)
    intro z hz
    have hz' : z ∈ cfgT c.R M ⊓ Subgroup.centralizer (c.D : Set G) :=
      ⟨hWT' (mem_centerOf_iff.1 hz).1, h1 hz⟩
    rw [T_inf_centralizer_D c hNM] at hz'
    exact hR0U hz'
  obtain ⟨hVes, hVZ⟩ := central_product_es hWU hUes hWes hZW
  have hWU1 : ⁅U2 ⊓ cx a, c.D⁆ ≤ cfgT c.R M ⊓ Subgroup.centralizer (U : Set G) := le_inf hWT' hWU
  have hU1W : ⁅cfgT c.R M ⊓ Subgroup.centralizer (U : Set G), ⁅U2 ⊓ cx a, c.D⁆⁆ ≤ U :=
    (Subgroup.commutator_mono le_rfl (hWle.trans inf_le_left)).trans hU2c
  have hTV := comm_T_V hUT hgen hWU1 hU1W (es_basic hUes).2.2.1 hVZ
  have hVT : U ⊔ ⁅U2 ⊓ cx a, c.D⁆ ≤ cfgT c.R M := sup_le hUT hWT'
  refine ⟨U ⊔ ⁅U2 ⊓ cx a, c.D⁆, ⟨hVT, Or.inl hVes, i312 hVT hVes hTV, le_normalizer_sup' hAU hWn,
    hR0U.trans le_sup_left⟩, Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => haW ?_)⟩
  rw [h]
  exact le_sup_right

theorem goodU_T {T R0 A : Subgroup G} (h0 : GoodU T R0 A R0)
    (hstep : ∀ U : Subgroup G, GoodU T R0 A U → U ≠ T →
      ∃ V : Subgroup G, GoodU T R0 A V ∧ Nat.card U < Nat.card V) : GoodU T R0 A T := by
  suffices h : ∀ n : ℕ, ∀ U : Subgroup G, GoodU T R0 A U → Nat.card T - Nat.card U ≤ n →
      GoodU T R0 A T from h _ R0 h0 le_rfl
  intro n
  induction n with
  | zero =>
    intro U hU hn
    have heq : U = T := Subgroup.eq_of_le_of_card_ge hU.1 (by omega)
    rwa [heq] at hU
  | succ n ih =>
    intro U hU hn
    by_cases hUT : U = T
    · rwa [hUT] at hU
    obtain ⟨V, hV, hlt⟩ := hstep U hU hUT
    have hVle : Nat.card V ≤ Nat.card T := Subgroup.card_le_of_le hV.1
    exact ih V hV (by omega)

theorem T_es (hc : S8Ctx G p) (hin : Inputs89 G p) (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row) {M : Subgroup G}
    (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) : IsExtraSpec2 (cfgT c.R M) := by
  have h0 : GoodU (cfgT c.R M) (cfgR0 c.R c.D) (cfgK p x L c.D c.R ⊔ c.Bs) (cfgR0 c.R c.D) :=
    ⟨inf_le_left.trans le_sup_left, c.hR0, T_le_R0_cen hc hin hx hL hrow c hNM,
      cfg_KB_le_normalizer_R0 c, le_rfl⟩
  have hT := goodU_T h0 fun U hU hne => goodU_step hc hin hx hL hrow c hNM hU hne
  rcases hT.2.1 with h | h
  · exact h
  · exfalso
    have hRT : Nat.card c.R ≤ Nat.card (cfgT c.R M) := Subgroup.card_le_of_le le_sup_left
    rw [h, c.hR.2] at hRT
    have h5 : 5 ≤ row.rexp := by cases row <;> decide
    have : 2 ^ 5 ≤ 2 ^ row.rexp := Nat.pow_le_pow_right (by norm_num) h5
    omega

end Para3

theorem lemma810 {p : ℕ} {x : G} {L : Subgroup G} {row : Row} (hc : S8Ctx G p) (hin : Inputs89 G p)
    (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row)
    {M : Subgroup G} (hM : GLAIsMaxTwoLocal M) (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) :
    pCoreOf 2 M = cfgT c.R M ∧ IsExtraSpec2 (cfgT c.R M) := by
  have hT := T_es hc hin hx hL hrow c hNM
  exact ⟨S_eq_T hc hin hx hL hrow c hM hNM hT, hT⟩

end L89

end S8

end CFSG.LocalAnalysis.GLTheoremA

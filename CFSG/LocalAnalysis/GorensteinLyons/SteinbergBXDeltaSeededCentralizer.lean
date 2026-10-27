module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXDeltaFailureWitness
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMLocalPrimeSetRankFour
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.LargeEvenClassification.Helpers
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsDeltaSeedWitness (p : ℕ) (B D₀ S₀ : Subgroup G) : Prop :=
  ∃ K₀ : Subgroup G, (5 ≤ p → K₀ = GLADelta p D₀) ∧ (p = 3 → K₀ = ⁅GLADelta p D₀, B⁆) ∧
    (∃ Q : Sylow 2 K₀, (Q : Subgroup K₀).map K₀.subtype = S₀) ∧ S₀ ≠ ⊥ ∧
    B ≤ normalizer (S₀ : Set G) ∧ S₀ ≤ GLADelta p D₀ ∧ D₀ ≤ B ⊓ centralizer (S₀ : Set G)

@[expose] def deltaSeededFamily [Finite G] (p : ℕ) (B S₀ : Subgroup G) : Set (Subgroup G) :=
  {R | IsPGroup 2 R ∧ S₀ ≤ R ∧ B ≤ normalizer (R : Set G) ∧
    2 ≤ CFSG.Open.pRank p (B ⊓ centralizer (R : Set G))}

theorem isElemAbelian_of_le_elem {p : ℕ} {B E : Subgroup G} (hEB : E ≤ B)
    (hB : IsElemAbelian p B) : IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hB hEB

theorem isPGroup_of_isElemAbelian' {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem two_le_pRank_of_plane [Finite G] {p : ℕ} (hp : 1 < p) {C E : Subgroup G} (hEC : E ≤ C)
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) : 2 ≤ CFSG.Open.pRank p C :=
  CFSG.SectionRank.le_pRank hp hEC hE hEcard

theorem mem_normalizer_sup_of_mem {S T : Subgroup G} {g : G} (hS : g ∈ normalizer (S : Set G))
    (hT : g ∈ normalizer (T : Set G)) : g ∈ normalizer ((S ⊔ T : Subgroup G) : Set G) := by
  have key : ∀ h : G, h ∈ normalizer (S : Set G) → h ∈ normalizer (T : Set G) →
      ∀ y ∈ S ⊔ T, h * y * h⁻¹ ∈ S ⊔ T := by
    intro h hhS hhT y hy
    have hle : S ⊔ T ≤ (S ⊔ T).comap (MulAut.conj h).toMonoidHom := by
      refine sup_le (fun s hs => ?_) (fun t ht => ?_)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left ((mem_normalizer_iff.mp hhS s).mp hs)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_right ((mem_normalizer_iff.mp hhT t).mp ht)
    have := hle hy
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hS hT y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hS) (inv_mem hT) _ hy
  simpa [mul_assoc] using this

theorem mem_normalizer_centralizer_of_mem' {L : Subgroup G} {g : G}
    (hg : g ∈ normalizer (L : Set G)) : g ∈ normalizer (centralizer (L : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hy l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      simpa using (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
    have := hy _ hl'
    calc l * (g * y * g⁻¹) = g * ((g⁻¹ * l * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * l * g)) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * l := by group
  · intro hy l hl
    have hl' : g * l * g⁻¹ ∈ L := (mem_normalizer_iff.mp hg l).mp hl
    have := hy _ hl'
    calc l * y = g⁻¹ * ((g * l * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * l * g⁻¹)) * g := by rw [this]
      _ = y * l := by group

theorem mem_normalizer_inf_of_mem' {S T : Subgroup G} {g : G} (hS : g ∈ normalizer (S : Set G))
    (hT : g ∈ normalizer (T : Set G)) : g ∈ normalizer ((S ⊓ T : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hS hT ⊢
  intro x
  rw [mem_inf, mem_inf, hS x, hT x]

theorem isPGroup_inSubgroup_pCore (p : ℕ) (Y : Subgroup G) :
    IsPGroup p (CFSG.inSubgroup (CFSG.pCore p) Y) :=
  CFSG.pCore_isPGroup.map Y.subtype

theorem le_normalizer_inSubgroup_pCore (p : ℕ) (Y : Subgroup G) :
    Y ≤ normalizer (CFSG.inSubgroup (CFSG.pCore p) Y : Set G) := by
  have h := le_normalizer_map (H := CFSG.pCore p Y) Y.subtype
  rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

theorem le_inSubgroup_pCore_of_normal {p : ℕ} {Y T : Subgroup G} (hTY : T ≤ Y)
    (hTn : (T.subgroupOf Y).Normal) (hT : IsPGroup p T) :
    T ≤ CFSG.inSubgroup (CFSG.pCore p) Y := by
  have hle : T.subgroupOf Y ≤ CFSG.pCore p Y :=
    le_sSup ⟨hTn, hT.comap_of_injective Y.subtype Y.subtype_injective⟩
  have h := map_mono (f := Y.subtype) hle
  rwa [subgroupOf_map_subtype, inf_of_le_left hTY] at h

theorem le_inSubgroup_pCore_of_le_centralizer {p : ℕ} {Y X : Subgroup G}
    (hY : IsCharacteristicP p Y) (hXY : X ≤ Y)
    (hXC : X ≤ centralizer (CFSG.inSubgroup (CFSG.pCore p) Y : Set G)) :
    X ≤ CFSG.inSubgroup (CFSG.pCore p) Y := by
  intro x hx
  have hxc : (⟨x, hXY hx⟩ : Y) ∈ centralizer (CFSG.pCore p Y : Set Y) := by
    rw [mem_centralizer_iff]
    intro q hq
    exact Subtype.ext (mem_centralizer_iff.mp (hXC hx) q ⟨q, hq, rfl⟩)
  exact ⟨_, hY hxc, rfl⟩

theorem inSubgroup_pCore_ne_bot_of_isPLocal {Y : Subgroup G} (hY : IsPLocal 2 Y) :
    CFSG.inSubgroup (CFSG.pCore 2) Y ≠ ⊥ := by
  obtain ⟨T, hT1, hT2, rfl⟩ := hY
  intro h
  have hle := le_inSubgroup_pCore_of_normal le_normalizer normal_in_normalizer hT2
  rw [h, le_bot_iff] at hle
  exact hT1 hle

theorem eq_bot_of_isPGroup_of_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X Q : Subgroup G}
    (hX : IsPGroup p X) (hQ : IsPGroup 2 Q) (hXQ : X ≤ Q) : X = ⊥ := by
  have := Fact.mk hp
  have := Fact.mk Nat.prime_two
  have hdisj := IsPGroup.disjoint_of_ne p 2 hp2 X Q hX hQ
  exact le_bot_iff.mp fun x hx => hdisj.le_bot (mem_inf.mpr ⟨hx, hXQ hx⟩)

theorem le_of_forall_hyperplane_centralizer_le [Finite G] {p : ℕ} (hp : p.Prime)
    {A₀ Q X : Subgroup G} (hA₀ : IsElemAbelian p A₀) (hA₀1 : A₀ ≠ ⊥)
    (hQA : A₀ ≤ normalizer (Q : Set G)) (hQp : ¬ p ∣ Nat.card Q)
    (hX : ∀ E : Subgroup G, E ≤ A₀ → E.relIndex A₀ = p → Q ⊓ centralizer (E : Set G) ≤ X) :
    Q ≤ X := by
  have := Fact.mk hp
  have hconj : ∀ a ∈ A₀, ∀ r ∈ Q, a * r * a⁻¹ ∈ Q := fun a ha r hr =>
    (mem_normalizer_iff.mp (hQA ha) r).mp hr
  let _ : MulDistribMulAction A₀ Q :=
    { smul := fun a r => ⟨a * r * a⁻¹, hconj a a.2 r r.2⟩
      one_smul := fun r => Subtype.ext (by
        change ((1 : A₀) : G) * (r : G) * ((1 : A₀) : G)⁻¹ = r
        simp)
      mul_smul := fun a b r => Subtype.ext (by
        change ((a * b : A₀) : G) * (r : G) * ((a * b : A₀) : G)⁻¹ =
          (a : G) * ((b : G) * (r : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc])
      smul_mul := fun a r s => Subtype.ext (by
        change (a : G) * ((r * s : Q) : G) * (a : G)⁻¹ =
          (a : G) * (r : G) * (a : G)⁻¹ * ((a : G) * (s : G) * (a : G)⁻¹)
        simp [mul_assoc])
      smul_one := fun a => Subtype.ext (by
        change (a : G) * ((1 : Q) : G) * (a : G)⁻¹ = ((1 : Q) : G)
        simp) }
  have : CFSG.IsElementaryAbelian p A₀ :=
    { toIsMulCommutative := hA₀.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA₀.2 x x.2) }
  have : Nontrivial A₀ := (Subgroup.nontrivial_iff_ne_bot A₀).mpr hA₀1
  have key := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := A₀) (H := Q) hQp
  have hle : (⨆ (B : Subgroup A₀) (_ : B.index = p), CFSG.fixedPointSubgroup B Q) ≤
      X.comap Q.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    have hE : B.map A₀.subtype ≤ A₀ := map_subtype_le B
    have hEidx : (B.map A₀.subtype).relIndex A₀ = p := by
      rw [relIndex, subgroupOf, comap_map_eq_self_of_injective A₀.subtype_injective, hB]
    refine hX _ hE hEidx (mem_inf.mpr ⟨x.2, ?_⟩)
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have h1 : ((⟨b, hb⟩ : B) • x : Q) = x := hx ⟨b, hb⟩
    have h2 := congrArg Subtype.val h1
    change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at h2
    calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (x : G) * (b : G) := by rw [h2]
  intro r hr
  have hr' : (⟨r, hr⟩ : Q) ∈ (⊤ : Subgroup Q) := trivial
  rw [← key] at hr'
  exact hle hr'

theorem delta_seeded_maximal_local_rank_two_centralizer [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hchar : IsCharacteristicPType G 2) {p : ℕ}
    (hp : p ∈ GLABeta 4 G) (hfail : ¬ GLADeltaZero G p) :
    (∃ B : Subgroup G, GLAIsBmax p B ∧ ∃ D₀ : Subgroup G, D₀ ≤ B ∧ IsElemAbelian p D₀ ∧
      Nat.card D₀ = p ^ 2 ∧ ∃ S₀ : Subgroup G, IsDeltaSeedWitness p B D₀ S₀) ∧
    ∀ B D₀ S₀ : Subgroup G, GLAIsBmax p B → D₀ ≤ B → IsElemAbelian p D₀ → Nat.card D₀ = p ^ 2 →
      IsDeltaSeedWitness p B D₀ S₀ →
      (∃ S : Subgroup G, Maximal (· ∈ deltaSeededFamily p B S₀) S) ∧
      ∀ S : Subgroup G, Maximal (· ∈ deltaSeededFamily p B S₀) S →
        Nat.card (B ⊓ centralizer (S : Set G) : Subgroup G) = p ^ 2 ∧
        (∃ M : Subgroup G, M ∈ maximalTwoLocalsContaining (normalizer (S : Set G) : Set G)) ∧
        (∀ M ∈ maximalTwoLocalsContaining (normalizer (S : Set G) : Set G),
          M < ⊤ ∧ B ≤ normalizer (S : Set G) ∧ normalizer (S : Set G) ≤ M ∧
          p ∈ localPrimeSetRankFour G M ∧ IsCharacteristicP 2 (normalizer (S : Set G)) ∧
          IsCharacteristicP 2 M ∧ CFSG.inSubgroup (CFSG.pCore 2) M ≠ ⊥ ∧
          CFSG.inSubgroup (CFSG.pCore 2) M ⊓
              centralizer ((B ⊓ centralizer (S : Set G) : Subgroup G) : Set G) =
            S ⊓ CFSG.inSubgroup (CFSG.pCore 2) M) ∧
        (S.subgroupOf (normalizer (S : Set G))).Normal ∧
        S ≤ CFSG.inSubgroup (CFSG.pCore 2) (normalizer (S : Set G)) ∧
        CFSG.inSubgroup (CFSG.pCore 2) (normalizer (S : Set G)) ⊓
            centralizer ((B ⊓ centralizer (S : Set G) : Subgroup G) : Set G) = S ∧
        (∀ Y : Subgroup G, IsPLocal 2 Y → normalizer (S : Set G) ≤ Y →
          CFSG.inSubgroup (CFSG.pCore 2) Y ⊓
              centralizer ((B ⊓ centralizer (S : Set G) : Subgroup G) : Set G) =
            S ⊓ CFSG.inSubgroup (CFSG.pCore 2) Y) ∧
        S < CFSG.inSubgroup (CFSG.pCore 2) (normalizer (S : Set G)) := by
  classical
  have hpp : p.Prime := hp.1
  have hp2 : p ≠ 2 := hp.2.1
  have := Fact.mk hpp
  refine ⟨?_, fun B D₀ S₀ hB hD₀B hD₀ hD₀card hW => ?_⟩
  · obtain ⟨B, hB, D, hDB, hD, hDcard, S, K, hK5, hK3, -, hQ, hSne, hSΔ, hBS, hDS, -, -⟩ :=
      delta_failure_invariant_two_witness hpp hp2 hfail
    exact ⟨B, hB, D, hDB, hD, hDcard, S, K, hK5, hK3, hQ, hSne, hBS, hSΔ, le_inf hDB hDS⟩
  obtain ⟨K₀, -, -, ⟨Q₀, hQ₀⟩, hS₀ne, hBS₀, -, hD₀S₀⟩ := hW
  have hS₀2 : IsPGroup 2 S₀ := by
    rw [← hQ₀]
    exact Q₀.isPGroup'.map K₀.subtype
  have hS₀fam : S₀ ∈ deltaSeededFamily p B S₀ :=
    ⟨hS₀2, le_rfl, hBS₀, two_le_pRank_of_plane hpp.one_lt hD₀S₀ hD₀ hD₀card⟩
  refine ⟨(Set.toFinite _).exists_maximal ⟨S₀, hS₀fam⟩, fun S hS => ?_⟩
  obtain ⟨⟨hS2, hS₀S, hBS, hArank⟩, hSmax⟩ := hS
  set A := B ⊓ centralizer (S : Set G) with hAdef
  set H := normalizer (S : Set G) with hHdef
  have hSne : S ≠ ⊥ := fun h => hS₀ne (le_bot_iff.mp (h ▸ hS₀S))
  have hHloc : IsPLocal 2 H := ⟨S, hSne, hS2, rfl⟩
  have hBel : IsElemAbelian p B := hB.1
  have hAel : IsElemAbelian p A := isElemAbelian_of_le_elem inf_le_left hBel
  have hAB : A ≤ B := inf_le_left
  have hAS : A ≤ centralizer (S : Set G) := inf_le_right
  have hSA : S ≤ centralizer (A : Set G) := le_centralizer_iff.mp hAS
  have hAH : A ≤ H := hAB.trans hBS
  have hkey : ∀ Y : Subgroup G, IsPLocal 2 Y → H ≤ Y → ∀ E : Subgroup G, E ≤ A →
      IsElemAbelian p E → Nat.card E = p ^ 2 →
      CFSG.inSubgroup (CFSG.pCore 2) Y ⊓ centralizer (E : Set G) ≤ S := by
    intro Y _ hHY E hEA hE hEcard
    set Q := CFSG.inSubgroup (CFSG.pCore 2) Y with hQdef
    set T := Q ⊓ centralizer (E : Set G) with hTdef
    have hQ2 : IsPGroup 2 Q := isPGroup_inSubgroup_pCore 2 Y
    have hYQ : Y ≤ normalizer (Q : Set G) := le_normalizer_inSubgroup_pCore 2 Y
    have hES : E ≤ centralizer (S : Set G) := hEA.trans hAS
    have hSE : S ≤ centralizer (E : Set G) := le_centralizer_iff.mp hES
    have hST : S ≤ normalizer (T : Set G) := fun s hs =>
      mem_normalizer_inf_of_mem' (hYQ (hHY (le_normalizer hs)))
        (le_normalizer (hSE hs))
    have hR2 : IsPGroup 2 (S ⊔ T : Subgroup G) :=
      hS2.to_sup_of_normal_right' (hQ2.to_le inf_le_left) hST
    have hBE : B ≤ centralizer (E : Set G) := by
      intro b hb
      rw [mem_centralizer_iff]
      intro e he
      exact congrArg Subtype.val (hBel.1.is_comm.comm ⟨e, hEA.trans hAB he⟩ ⟨b, hb⟩)
    have hBR : B ≤ normalizer ((S ⊔ T : Subgroup G) : Set G) := fun b hb =>
      mem_normalizer_sup_of_mem (hBS hb)
        (mem_normalizer_inf_of_mem' (hYQ (hHY (hBS hb))) (le_normalizer (hBE hb)))
    have hER : E ≤ B ⊓ centralizer ((S ⊔ T : Subgroup G) : Set G) := by
      refine le_inf (hEA.trans hAB) (le_centralizer_iff.mpr (sup_le ?_ ?_))
      · exact hSE
      · exact inf_le_right
    have hRfam : S ⊔ T ∈ deltaSeededFamily p B S₀ :=
      ⟨hR2, hS₀S.trans le_sup_left, hBR, two_le_pRank_of_plane hpp.one_lt hER hE hEcard⟩
    exact le_sup_right.trans (hSmax hRfam le_sup_left)
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian' hAel
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hAp
  have ha2 : 2 ≤ a := by
    obtain ⟨E, hEA, -, hEcard⟩ := CFSG.LargeEvenClassification.Helpers.pRank_witness hpp.one_lt A
    have hdvd := card_dvd_of_le hEA
    rw [hEcard, ha] at hdvd
    have := (Nat.pow_dvd_pow_iff_le_right hpp.one_lt).mp hdvd
    omega
  have hQH2 : IsPGroup 2 (CFSG.inSubgroup (CFSG.pCore 2) H) := isPGroup_inSubgroup_pCore 2 H
  have hcharH : IsCharacteristicP 2 H := hchar H hHloc
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, card_bot] at ha
    have := Nat.one_lt_pow (by omega : a ≠ 0) hpp.one_lt
    omega
  have hnotC : ∀ Y : Subgroup G, IsPLocal 2 Y → H ≤ Y →
      ¬ A ≤ centralizer (CFSG.inSubgroup (CFSG.pCore 2) Y : Set G) := by
    intro Y hY hHY hAC
    have hAQ := le_inSubgroup_pCore_of_le_centralizer (hchar Y hY) (hAH.trans hHY) hAC
    exact hAne (eq_bot_of_isPGroup_of_le hpp hp2 hAp (isPGroup_inSubgroup_pCore 2 Y) hAQ)
  have hA2 : a = 2 := by
    by_contra hne
    have ha3 : 3 ≤ a := by omega
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 3)
      (by rw [ha]; exact Nat.pow_dvd_pow p ha3)
    set A₀ := K.map A.subtype with hA₀def
    have hA₀A : A₀ ≤ A := map_subtype_le K
    have hA₀card : Nat.card A₀ = p ^ 3 := by
      rw [hA₀def, card_map_of_injective A.subtype_injective, hK]
    have hA₀el : IsElemAbelian p A₀ := isElemAbelian_of_le_elem hA₀A hAel
    have hA₀ne : A₀ ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hA₀card
      have := Nat.one_lt_pow (by norm_num : (3 : ℕ) ≠ 0) hpp.one_lt
      omega
    have hQp : ¬ p ∣ Nat.card (CFSG.inSubgroup (CFSG.pCore 2) H) := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQH2
      rw [hm]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h))
    have hQS : CFSG.inSubgroup (CFSG.pCore 2) H ≤ S := by
      refine le_of_forall_hyperplane_centralizer_le hpp hA₀el hA₀ne
        (hA₀A.trans (hAH.trans (le_normalizer_inSubgroup_pCore 2 H))) hQp ?_
      intro E hEA₀ hEidx
      have hEcard : Nat.card E = p ^ 2 := by
        have h1 := card_mul_index (E.subgroupOf A₀)
        rw [Nat.card_congr (subgroupOfEquivOfLe hEA₀).toEquiv, ← relIndex, hEidx,
          hA₀card] at h1
        rw [pow_succ] at h1
        exact Nat.eq_of_mul_eq_mul_right hpp.pos h1
      exact hkey H hHloc le_rfl E (hEA₀.trans hA₀A) (isElemAbelian_of_le_elem hEA₀ hA₀el) hEcard
    exact hnotC H hHloc le_rfl (fun x hx => centralizer_le hQS (hAS hx))
  have hAcard : Nat.card A = p ^ 2 := by rw [ha, hA2]
  have hCY : ∀ Y : Subgroup G, IsPLocal 2 Y → H ≤ Y →
      CFSG.inSubgroup (CFSG.pCore 2) Y ⊓ centralizer (A : Set G) =
        S ⊓ CFSG.inSubgroup (CFSG.pCore 2) Y := by
    intro Y hY hHY
    apply le_antisymm
    · exact le_inf (hkey Y hY hHY A le_rfl hAel hAcard) inf_le_left
    · exact le_inf inf_le_right (inf_le_left.trans hSA)
  have hSQH : S ≤ CFSG.inSubgroup (CFSG.pCore 2) H :=
    le_inSubgroup_pCore_of_normal le_normalizer normal_in_normalizer hS2
  have hCH : CFSG.inSubgroup (CFSG.pCore 2) H ⊓ centralizer (A : Set G) = S := by
    rw [hCY H hHloc le_rfl, inf_of_le_left hSQH]
  have hMex : ∃ M : Subgroup G, M ∈ maximalTwoLocalsContaining (H : Set G) := by
    obtain ⟨M, ⟨hMloc, hHM⟩, hMmax⟩ :=
      (Set.toFinite {Y : Subgroup G | IsPLocal 2 Y ∧ H ≤ Y}).exists_maximal ⟨H, hHloc, le_rfl⟩
    refine ⟨M, ⟨hMloc, fun Y hMY hY => ?_⟩, hHM⟩
    exact absurd (hMmax ⟨hY, hHM.trans hMY.le⟩ hMY.le) (not_le_of_gt hMY)
  refine ⟨hAcard, hMex, fun M hM => ?_, normal_in_normalizer, hSQH, hCH,
    fun Y hY hHY => hCY Y hY hHY, lt_of_le_of_ne hSQH fun h => ?_⟩
  · obtain ⟨⟨hMloc, -⟩, hHM⟩ := hM
    have hHM' : H ≤ M := hHM
    refine ⟨lt_top_iff_ne_top.mpr (CFSG.LargeEvenClassification.Helpers.twoLocal_ne_top G hnab
      M hMloc), hBS, hHM', ⟨hp, B, hB, hBS.trans hHM'⟩, hcharH, hchar M hMloc,
      inSubgroup_pCore_ne_bot_of_isPLocal hMloc, hCY M hMloc hHM'⟩
  · apply hnotC H hHloc le_rfl
    rw [← h]
    exact hAS

end CFSG.LocalAnalysis.GorensteinLyons

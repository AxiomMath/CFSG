module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank

theorem pPrimeCore_quotient_eq_bot (X : Type*) [Group X] [Finite X] :
    pPrimeCore 2 (X ⧸ pPrimeCore 2 X) = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro H hH hcop
  set N : Subgroup X := pPrimeCore 2 X with hN
  let P : Subgroup X := H.comap (QuotientGroup.mk' N)
  have hP : P.Normal := hH.comap _
  have hcard : Nat.card P = Nat.card N * Nat.card H :=
    QuotientGroup.card_preimage_mk N (H : Set (X ⧸ N))
  have hPcop : Nat.Coprime 2 (Nat.card P) := by
    rw [hcard]
    exact Nat.Coprime.mul_right pPrimeCore_coprime_card hcop
  have hPN : P ≤ N := le_sSup ⟨hP, hPcop⟩
  have hH' : H = P.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_comap_eq,
      MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective N), top_inf_eq]
  rw [hH', eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  have : x ∈ N := hPN hx
  simp [QuotientGroup.eq_one_iff, this]

theorem pPrimeCoreOf_le_of_normal {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    {H K : Subgroup X} (hle : H ≤ K) (hN : (H.subgroupOf K).Normal) :
    pPrimeCoreOf p H ≤ pPrimeCoreOf p K := by
  set H' : Subgroup ↥K := H.subgroupOf K with hH'
  have : H'.Normal := hN
  let e : ↥H' ≃* ↥H := Subgroup.subgroupOfEquivOfLe hle
  have hA : ((pPrimeCore p ↥H').map H'.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hAcop : Nat.Coprime p (Nat.card ↥((pPrimeCore p ↥H').map H'.subtype)) := by
    rw [Subgroup.card_map_of_injective H'.subtype_injective]
    exact pPrimeCore_coprime_card
  have hAle : (pPrimeCore p ↥H').map H'.subtype ≤ pPrimeCore p ↥K := le_sSup ⟨hA, hAcop⟩
  have hid : pPrimeCoreOf p H = ((pPrimeCore p ↥H').map H'.subtype).map K.subtype := by
    unfold pPrimeCoreOf
    rw [Subgroup.map_map, ← pPrimeCore_map_iso p e, Subgroup.map_map]
    rfl
  rw [hid]
  exact Subgroup.map_mono hAle

theorem pPrimeCoreOf_le_of_subnormal {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    {H : Subgroup X} (hH : H.IsSubnormal) : pPrimeCoreOf p H ≤ pPrimeCore p X := by
  induction hH with
  | top =>
    have h := pPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
    unfold pPrimeCoreOf
    exact h.le
  | step H K hle hK hN ih =>
    exact (pPrimeCoreOf_le_of_normal p hle hN).trans ih

theorem le_pPrimeCore_of_subnormal {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    {A : Subgroup X} (hA : A.IsSubnormal) (hcop : Nat.Coprime p (Nat.card A)) :
    A ≤ pPrimeCore p X := by
  refine le_trans ?_ (pPrimeCoreOf_le_of_subnormal p hA)
  have h : (⊤ : Subgroup ↥A) ≤ pPrimeCore p ↥A := by
    refine le_sSup ⟨inferInstance, ?_⟩
    simpa using hcop
  intro a ha
  exact ⟨⟨a, ha⟩, h (Subgroup.mem_top _), rfl⟩

theorem isPGroup_two_center_of_subnormal {X : Type*} [Group X] [Finite X]
    (hX : pPrimeCore 2 X = ⊥) {K : Subgroup X} (hK : K.IsSubnormal) :
    IsPGroup 2 ↥(center ↥K) := by
  rintro ⟨z, hz⟩
  have hn0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  set z0 : ↥K := z ^ (2 ^ a) with hz0
  have hz0ord : orderOf z0 = m := by
    have := orderOf_pow_of_dvd (x := z) (n := 2 ^ a) (by positivity) (hn ▸ Dvd.intro _ rfl)
    rw [hz0, this, hn]
    simp [Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ a)]
  have hz0central : z0 ∈ center ↥K := Subgroup.pow_mem _ hz _
  let Z0 : Subgroup ↥K := Subgroup.zpowers z0
  have hZ0le : Z0 ≤ center ↥K := (Subgroup.zpowers_le).mpr hz0central
  have hZ0n : Z0.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := Subgroup.mem_center_iff.mp (hZ0le hn) g
    rw [this, mul_inv_cancel_right]
    exact hn
  set Z1 : Subgroup X := Z0.map K.subtype with hZ1
  have hZ1sub : Z1.IsSubnormal := by
    refine Subgroup.IsSubnormal.step Z1 K ?_ hK ?_
    · rintro _ ⟨k, -, rfl⟩
      exact k.2
    · have : Z1.subgroupOf K = Z0 :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective Z0
      rw [this]
      exact hZ0n
  have hcard : Nat.card Z1 = m := by
    rw [hZ1, Subgroup.card_map_of_injective K.subtype_injective, Nat.card_zpowers, hz0ord]
  have hcop : Nat.Coprime 2 (Nat.card Z1) := by
    rw [hcard]
    exact Nat.coprime_two_left.mpr hm
  have hle := le_pPrimeCore_of_subnormal 2 hZ1sub hcop
  rw [hX, le_bot_iff] at hle
  have hZ0bot : Z0 = ⊥ :=
    Subgroup.map_injective K.subtype_injective (by rw [Subgroup.map_bot]; exact hle)
  have hz01 : z0 = 1 := by
    have : z0 ∈ Z0 := Subgroup.mem_zpowers z0
    rw [hZ0bot, Subgroup.mem_bot] at this
    exact this
  have hm1 : m = 1 := by rw [← hz0ord, hz01, orderOf_one]
  refine ⟨a, Subtype.ext ?_⟩
  have : z ^ (2 ^ a) = 1 := by
    have h1 : orderOf z = 2 ^ a := by rw [hn, hm1, mul_one]
    rw [← h1]
    exact pow_orderOf_eq_one z
  simpa using this

theorem isKGroupNative_of_surjective {X Y : Type} [Group X] [Group Y] (hX : IsKGroupNative X)
    (L : Subgroup X) (φ : L →* Y) (hφ : Function.Surjective φ) : IsKGroupNative Y :=
  SectionRank.IsKGroupCat.of_mulEquiv
    ((SectionRank.IsKGroupCat.subgroup hX L).quotient φ.ker)
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm

theorem centralizer_involution_ne_top {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) {x : G} (hx : orderOf x = 2) :
    centralizer ({x} : Set G) ≠ ⊤ := by
  intro h
  have hxc : x ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({x} : Set G) := h ▸ Subgroup.mem_top g
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this x rfl).symm
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.mem_bot] at hxc
    rw [hxc, orderOf_one] at hx
    omega
  · obtain ⟨a, b, hab⟩ := hn
    exact hab ((Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b)) a)

theorem inCalK2_of_isComponent {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G)
    {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hK : IsComponent K) :
    InCalK2 ↥K := by
  obtain ⟨hs, hn, hKP⟩ := hG
  refine ⟨hK.1, ?_, ?_⟩
  · have hX : pPrimeCore 2 (CentralizerBar x) = ⊥ :=
      pPrimeCore_quotient_eq_bot (↥(centralizer ({x} : Set G)))
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, isPGroup_two_center_of_subnormal hX hK.2⟩
    · have hN : (pCore 2 ↥K).Normal := inferInstance
      rcases LocalCores.quasisimple_normal_subgroups hK.1 hN with h | h
      · exfalso
        have hP : IsPGroup 2 ↥K := by
          have := pCore_isPGroup (p := 2) (G := ↥K)
          rw [h] at this
          exact this.of_equiv (Subgroup.topEquiv (G := ↥K))
        have : Group.IsNilpotent ↥K := hP.isNilpotent
        have : Nontrivial ↥K := LocalCores.isQuasisimple_nontrivial hK.1
        have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K
        have : Group.IsPerfect ↥K := hK.1.1
        have h2 : commutator ↥K = ⊤ := Group.IsPerfect.commutator_eq_top
        rw [h2] at h1
        exact lt_irrefl _ h1
      · exact h
  · have hC : IsKGroupNative ↥(centralizer ({x} : Set G)) :=
      isKGroupNative_of_kProper hKP (centralizer_involution_ne_top hs hn hx)
    let M := pPrimeCore 2 ↥(centralizer ({x} : Set G))
    let L : Subgroup ↥(centralizer ({x} : Set G)) := K.comap (QuotientGroup.mk' M)
    let φ : L →* ↥K := ((QuotientGroup.mk' M).comp L.subtype).codRestrict K fun y => y.2
    have hφ : Function.Surjective φ := fun k => by
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective M (k : CentralizerBar x)
      exact ⟨⟨y, show QuotientGroup.mk' M y ∈ K by rw [hy]; exact k.2⟩, Subtype.ext hy⟩
    exact isKGroupNative_of_surjective hC L φ hφ

theorem l2Sub_of_not_l2Meets_g2 {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G)
    (h : ¬ L2Meets G InG2) : L2Sub G (fun K _ => InC2 K ∨ InT2 K) := by
  intro x hx K hK
  by_contra hcon
  rw [not_or] at hcon
  exact h ⟨x, hx, K, hK, ⟨inCalK2_of_isComponent hG hx hK, hcon.1, hcon.2⟩⟩

theorem neg_one_ne_one_of_odd_card (F : Type) [Field F] [Finite F] (h : Odd (Nat.card F)) :
    (-1 : F) ≠ 1 := by
  apply Ring.neg_one_ne_one_of_char_ne_two
  intro h2
  have hc : CharP F 2 := by rw [← h2]; exact ringChar.charP F
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn] at h
  have : Even (2 ^ (n : ℕ)) := (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  exact (Nat.not_even_iff_odd.mpr h) this

theorem center_statedSL_two_ne_bot (F : Type) [Field F] [Finite F] (h : Odd (Nat.card F)) :
    center (StatedSL 2 F) ≠ ⊥ := by
  let m : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ)
  have hmat : (m : Matrix (Fin 2) (Fin 2) F) = -1 := by
    ext i j
    simp [m, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hdet : (m : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [hmat, Matrix.det_neg]
    simp
  have hm : m ∈ StatedSL 2 F := Subgroup.subset_closure hdet
  have hmc : m ∈ center (GL (Fin 2) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  intro hbot
  have hcent : (⟨m, hm⟩ : StatedSL 2 F) ∈ center (StatedSL 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hmc g)
  rw [hbot, Subgroup.mem_bot] at hcent
  have h1 : (m : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg
      (fun z : StatedSL 2 F => ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hcent
    simpa using this
  rw [hmat] at h1
  have h0 := congrFun (congrFun h1 0) 0
  simp at h0
  exact neg_one_ne_one_of_odd_card F h h0

theorem inT2_cases_of_center_bot {K : Type} [Group K] (hT : InT2 K) (hz : center K = ⊥) :
    HasL2Model K (fun q => Odd q ∧ ¬ IsFM9 q) ∨ Nonempty (K ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨-, h | h | h | h | h⟩ := hT
  · exact Or.inl h
  · exfalso
    obtain ⟨F, _, _, hodd, ⟨e⟩⟩ := h
    apply center_statedSL_two_ne_bot F hodd
    have := Subgroup.map_center_eq e
    rw [hz, Subgroup.map_bot] at this
    exact this.symm
  · exact Or.inr h
  · exfalso
    obtain ⟨n, -, -, hn⟩ := h
    have := hn.2.1
    rw [hz, Subgroup.card_bot] at this
    omega
  · exfalso
    obtain ⟨-, hexp⟩ := h
    rw [hz] at hexp
    have : Subsingleton ↥(⊥ : Subgroup K) := inferInstance
    rw [Monoid.exp_eq_one_of_subsingleton] at hexp
    omega

theorem inU2_of_inT2_of_center_bot {K : Type} [Group K] (hT : InT2 K) (hz : center K = ⊥) :
    InU2 K := by
  refine ⟨hT.1, ?_⟩
  rcases inT2_cases_of_center_bot hT hz with ⟨p, f, hp, hf, ⟨hodd, -⟩, hL⟩ | h
  · exact Or.inl ⟨p, f, hp, hf, hodd, hL⟩
  · exact Or.inr (Or.inl h)

theorem isFM9_odd {q : ℕ} (h : IsFM9 q) : Odd q := by
  rcases h with rfl | ⟨hp, ⟨k, hk⟩ | ⟨n, hn⟩⟩
  · exact ⟨4, rfl⟩
  · subst hk
    have : Even (2 ^ 2 ^ k) := Nat.even_pow.mpr ⟨even_two, by positivity⟩
    exact this.add_one
  · have h2 := hp.two_le
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hn
      omega
    have hev : Even (q + 1) := by
      rw [hn]
      exact Nat.even_pow.mpr ⟨even_two, hn0⟩
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hev)

theorem hasL2Model_odd_gt_three {K : Type} [Group K] {P : ℕ → Prop} (hP : ∀ q, P q → Odd q)
    (h : HasL2Model K P) : HasL2Model K (fun q => Odd q ∧ 3 < q) := by
  obtain ⟨p, f, hp, hf, hPq, hL⟩ := h
  have hadm : StatedLieAdmissible .PSL 2 p f := by
    rcases hL with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc.1
    all_goals exact absurd h0 (by norm_num)
  have h3 : p ^ f ≠ 3 := fun h3 => hadm.2.2.2.2 (by rw [h3])
  have hodd : Odd (p ^ f) := hP _ hPq
  have h2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨k, hk⟩ := hodd
  exact ⟨p, f, hp, hf, ⟨⟨k, hk⟩, by omega⟩, hL⟩

theorem isSubnormal_comap {A B : Type*} [Group A] [Group B] (f : A →* B) {H : Subgroup B}
    (hH : H.IsSubnormal) : (H.comap f).IsSubnormal := by
  induction hH with
  | top => simp
  | step H K hle hK hN ih =>
    refine Subgroup.IsSubnormal.step _ (K.comap f) (Subgroup.comap_mono hle) ih ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.comap_mono hle)]
    have hN' := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.mp (hN' hg) (f h)
    simpa using this

theorem ker_restrict_eq_pPrimeCore {C : Type*} [Group C] [Finite C] {L : Subgroup C}
    (hL : L.IsSubnormal) :
    ((QuotientGroup.mk' (pPrimeCore 2 C)).comp L.subtype).ker = pPrimeCore 2 ↥L := by
  set N : Subgroup C := pPrimeCore 2 C with hN
  apply le_antisymm
  · set ker := ((QuotientGroup.mk' N).comp L.subtype).ker with hker
    have hnorm : ker.Normal := MonoidHom.normal_ker _
    have hcop : Nat.Coprime 2 (Nat.card ker) := by
      have hmem : ∀ y : ker, ((y : L) : C) ∈ N := by
        intro y
        have := y.2
        rw [MonoidHom.mem_ker] at this
        exact (QuotientGroup.eq_one_iff _).mp this
      have hinj : Function.Injective (fun y : ker => (⟨((y : L) : C), hmem y⟩ : N)) := by
        intro a b hab
        have := congrArg (fun z : N => (z : C)) hab
        exact Subtype.ext (Subtype.ext this)
      have hdvd : Nat.card ker ∣ Nat.card N := by
        refine Subgroup.card_dvd_of_injective
          ({ toFun := fun y : ker => (⟨((y : L) : C), hmem y⟩ : N)
             map_one' := rfl
             map_mul' := fun _ _ => rfl } : ker →* N) hinj
      exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
    exact le_sSup ⟨hnorm, hcop⟩
  · intro l hl
    have h1 : (l : C) ∈ pPrimeCoreOf 2 L := ⟨l, hl, rfl⟩
    have h2 := pPrimeCoreOf_le_of_subnormal 2 hL h1
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr h2

theorem exists_pComponent_of_component {G : Type} [Group G] [Finite G] {x : G}
    {Kh : Subgroup (CentralizerBar x)} (hK : IsComponent Kh) :
    ∃ K : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K ∧
      Nonempty (↥K ⧸ pPrimeCore 2 ↥K ≃* ↥Kh) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  let π : ↥C →* CentralizerBar x := QuotientGroup.mk' (pPrimeCore 2 ↥C)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let S : Set (Subgroup ↥C) := {J | J.IsSubnormal ∧ J.map π = Kh}
  have hS : S.Nonempty :=
    ⟨Kh.comap π, isSubnormal_comap π hK.2, by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective _ hπ, top_inf_eq]⟩
  obtain ⟨L, hLS, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup ↥C)) S hS
  have hLpc : IsPComponent 2 L :=
    ⟨Kh, hK, hLS.1, hLS.2, fun J hJ hJs hJm => hmin J ⟨hJs, hJm⟩ hJ⟩
  refine ⟨L.map C.subtype, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨l, -, rfl⟩
    exact l.2
  · have : (L.map C.subtype).subgroupOf C = L :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective L
    rw [this]
    exact hLpc
  · set M : Subgroup G := L.map C.subtype with hM
    let e₁ : ↥L ≃* ↥M := L.equivMapOfInjective C.subtype C.subtype_injective
    have hmap : (pPrimeCore 2 ↥L).map e₁.toMonoidHom = pPrimeCore 2 ↥M :=
      pPrimeCore_map_iso 2 e₁
    let e₂ : (↥L ⧸ pPrimeCore 2 ↥L) ≃* (↥M ⧸ pPrimeCore 2 ↥M) :=
      QuotientGroup.congr _ _ e₁ hmap
    let φ : ↥L →* ↥Kh := (π.comp L.subtype).codRestrict Kh fun l => by
      rw [← hLS.2]
      exact ⟨l, l.2, rfl⟩
    have hφ : Function.Surjective φ := by
      intro k
      have hk : (k : CentralizerBar x) ∈ L.map π := by
        rw [hLS.2]
        exact k.2
      obtain ⟨c, hc, hck⟩ := hk
      exact ⟨⟨c, hc⟩, Subtype.ext hck⟩
    have hker : φ.ker = pPrimeCore 2 ↥L := by
      rw [MonoidHom.ker_codRestrict]
      exact ker_restrict_eq_pPrimeCore hLS.1
    let e₃ : (↥L ⧸ φ.ker) ≃* ↥Kh := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    let e₄ : (↥L ⧸ pPrimeCore 2 ↥L) ≃* (↥L ⧸ φ.ker) :=
      QuotientGroup.quotientMulEquivOfEq hker.symm
    exact ⟨e₂.symm.trans (e₄.trans e₃)⟩

end CFSG.GH74.GLS

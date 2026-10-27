module

public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.CGT.PushingUpLit.T2KSW.StrongEmb
import CFSG.Timmesfeld.Bridge.RootSetsSyl
import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped MatrixGroups

theorem exists_mulEquiv_SL2_of_isTI {Y : Type} [Group Y] [Finite Y]
    (P : Sylow 2 Y) {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card (P : Subgroup Y) = 2 ^ n)
    (hexp : ∀ a ∈ (P : Subgroup Y), a * a = 1) (hTI : fusionIsTI (P : Subgroup Y))
    (hne : Subgroup.normalizer ((P : Subgroup Y) : Set Y) ≠ ⊤)
    (hgen : ∀ N : Subgroup Y, (∀ y : Y, y * y = 1 → y ∈ N) → N = ⊤) :
    ∃ φ : Y ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      (P : Subgroup Y).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) := by
  classical
  have hq : 4 ≤ Nat.card (P : Subgroup Y) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have heven : Even (Nat.card (P : Subgroup Y)) := by
    rw [hcard]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hSE := CFSG.Timmesfeld.Bridge.fusionStronglyEmbedded_normalizer_of_isTI P hTI hne heven
  rcases CFSG.Open.bender_strongly_embedded_normal_series Y _ hSE with hcq |
    ⟨M, N, hMn, hNn, hMN', hMN, hModd, hNodd, hB⟩
  · exfalso
    rcases hcq P with hcyc | ⟨r, -, ⟨e⟩⟩
    · exact CFSG.Timmesfeld.Bridge.not_isCyclic_of_mul_self hexp hq hcyc
    · have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
      exact CFSG.Timmesfeld.Bridge.not_quaternion_of_mul_self hexp e
  have hNtop : N = ⊤ := hgen N fun y hy => by
    obtain ⟨j, hj⟩ := hNodd
    have hpow : y ^ N.index ∈ N := Subgroup.pow_index_mem N y
    rwa [hj, pow_succ, pow_mul, pow_two, hy, one_pow, one_mul] at hpow
  subst hNtop
  have hMH : M ≤ Subgroup.normalizer ((P : Subgroup Y) : Set Y) :=
    CFSG.Timmesfeld.Bridge.le_normalizer_of_isTI hexp hq hTI M hModd
  have hPM : (P : Subgroup Y) ⊓ M = ⊥ := disjoint_iff.1
    (Subgroup.disjoint_of_coprime_natCard (by
      rw [hcard]
      exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hModd)))
  have hcomm : ∀ a ∈ (P : Subgroup Y), ∀ m ∈ M, m * a = a * m :=
    fun a ha m hm => CFSG.Timmesfeld.Bridge.commute_of_le_normalizer hMH hPM ha hm
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hMinv : ∀ y : Y, y * y = 1 → ∀ m ∈ M, y * m = m * y := by
    intro y hy m hm
    have hdvd : orderOf y ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two, hy])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hp : IsPGroup 2 (Subgroup.zpowers y) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
    obtain ⟨h, -, hh⟩ := CFSG.CGT.PushingUpLit.T2KSW.exists_mem_conj_mem_of_isSylowOf hPtop
      (le_top : Subgroup.zpowers y ≤ ⊤) hp
    have hyP : h⁻¹ * y * h ∈ (P : Subgroup Y) := hh y (Subgroup.mem_zpowers y)
    have hmM : h⁻¹ * m * h ∈ M := by simpa using hMn.conj_mem m hm h⁻¹
    have h2 : (h⁻¹ * m * h) * (h⁻¹ * y * h) = (h⁻¹ * y * h) * (h⁻¹ * m * h) :=
      hcomm _ hyP _ hmM
    have h3 : h⁻¹ * (m * y) * h = h⁻¹ * (y * m) * h := by
      calc h⁻¹ * (m * y) * h = (h⁻¹ * m * h) * (h⁻¹ * y * h) := by group
        _ = (h⁻¹ * y * h) * (h⁻¹ * m * h) := h2
        _ = h⁻¹ * (y * m) * h := by group
    exact (mul_left_cancel (mul_right_cancel h3)).symm
  have hMc : M ≤ Subgroup.center Y := by
    have hC : Subgroup.centralizer (M : Set Y) = ⊤ := hgen _ fun y hy =>
      Subgroup.mem_centralizer_iff.2 fun m hm => (hMinv y hy m hm).symm
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (M : Set Y) := hC ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.1 hg m hm).symm
  set π : Y →* Y ⧸ M := QuotientGroup.mk' M with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective M
  have hQp : IsPGroup 2 ((P : Subgroup Y).map π) := P.isPGroup'.map π
  have hQi : ¬ 2 ∣ ((P : Subgroup Y).map π).index := by
    intro h
    exact P.not_dvd_index (h.trans (Subgroup.index_map_dvd _ hπsurj))
  have hQcomm : ∀ a ∈ (P : Subgroup Y).map π, ∀ b ∈ (P : Subgroup Y).map π, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact CFSG.Timmesfeld.Bridge.mul_comm_of_forall_mul_self hexp hx hy
  have hmapM : (M.subgroupOf (⊤ : Subgroup Y)).map
      (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).toMonoidHom = M := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hyM, rfl⟩
      exact hyM
    · intro hx
      exact ⟨⟨x, trivial⟩, hx, rfl⟩
  let eQ : (↥(⊤ : Subgroup Y) ⧸ M.subgroupOf (⊤ : Subgroup Y)) ≃* Y ⧸ M :=
    QuotientGroup.congr (M.subgroupOf (⊤ : Subgroup Y)) M Subgroup.topEquiv hmapM
  obtain ⟨f, hf, ⟨e⟩⟩ : ∃ f : ℕ, 2 ≤ f ∧ Nonempty (Y ⧸ M ≃* PSL(2, GaloisField 2 f)) := by
    rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact ⟨f, hf, ⟨eQ.symm.trans e⟩⟩
    · exfalso
      have e' : Y ⧸ M ≃* PSU3 2 f := eQ.symm.trans e
      have : Finite (PSU3 2 f) := Finite.of_surjective e' e'.surjective
      refine CFSG.Timmesfeld.Bridge.false_of_fusionBenderBorel
        ((bender_psu3_borel_full f hf).map_mulEquiv e'.symm) ?_ (by norm_num)
        (hQp.toSylow hQi) hQcomm
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exfalso
      have e' : Y ⧸ M ≃* Sz a := eQ.symm.trans e
      have : Finite (Sz a) := Finite.of_surjective e' e'.surjective
      refine CFSG.Timmesfeld.Bridge.false_of_fusionBenderBorel
        ((bender_suzuki_borel_full a ha).map_mulEquiv e'.symm) ?_ le_rfl
        (hQp.toSylow hQi) hQcomm
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcardK : Nat.card (Y ⧸ M) = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
    (Nat.card_congr e.toEquiv).trans
      (CFSG.Timmesfeld.Bridge.card_psl_two_galoisField_two f (by omega))
  have hcardY : Nat.card Y = Nat.card (Y ⧸ M) * Nat.card M := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup M]
  have hodd1 : Odd (((2 ^ f) ^ 2 - 1) * Nat.card M) := by
    refine Odd.mul (Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) ?_ odd_one) hModd
    exact Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, two_ne_zero⟩
  have hidx : Odd (P : Subgroup Y).index :=
    Nat.not_even_iff_odd.1 fun h => P.not_dvd_index (even_iff_two_dvd.1 h)
  have hfn : f = n := by
    have hY := (P : Subgroup Y).card_mul_index
    rw [hcardY, hcardK, hcard, mul_assoc] at hY
    have h1 : 2 ^ n = 2 ^ f := by
      apply Nat.dvd_antisymm
      · exact (Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd1)).dvd_of_dvd_mul_right
          (Dvd.intro _ hY)
      · exact (Nat.Coprime.pow_left f (Nat.coprime_two_left.2 hidx)).dvd_of_dvd_mul_right
          (Dvd.intro _ hY.symm)
    exact (Nat.pow_right_injective le_rfl h1).symm
  subst hfn
  have hMbot : M = ⊥ := by
    refine CFSG.Timmesfeld.RankOne.eq_bot_of_isCyclic_sylow hMc hModd
      (S := {y : Y | y * y = 1}) (hgen _ fun y hy => Subgroup.subset_closure hy)
      (fun s hs => hs) ?_
    intro r _ hr2 R
    have hcyc := isCyclic_sylow_psl2 hn r hr2
      (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective R)
    rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective R] at hcyc
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ e.injective)).2 hcyc
  let e₀ : Y ≃* Y ⧸ M :=
    ((QuotientGroup.quotientMulEquivOfEq hMbot).trans QuotientGroup.quotientBot).symm
  let φ₀ : Y ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
    e₀.trans (e.trans (psl2EquivSL2 (GaloisField 2 f)))
  set S := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)
  have hXS : Nat.card Y = Nat.card S := Nat.card_congr φ₀.toEquiv
  have hKn : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hPsyl : Nat.card (P : Subgroup Y) = 2 ^ (Nat.card Y).factorization 2 :=
    Sylow.card_eq_multiplicity P
  have hAsyl : Nat.card (upperUnipotent (GaloisField 2 f)) =
      2 ^ (Nat.card S).factorization 2 := by
    rw [card_upperUnipotent, hKn, ← hXS, ← hPsyl, hcard]
  let U : Sylow 2 S := Sylow.ofCard (upperUnipotent (GaloisField 2 f)) hAsyl
  let P' : Sylow 2 S := Sylow.mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective P
  have hP' : (P' : Subgroup S) = (P : Subgroup Y).map φ₀.toMonoidHom := by
    simp [P', Sylow.coe_mapSurjective]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P' U
  have hgU : ((P : Subgroup Y).map φ₀.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      upperUnipotent (GaloisField 2 f) := by
    have := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, hP', Sylow.coe_ofCard] at this
    exact this
  refine ⟨φ₀.trans (MulAut.conj g), ?_⟩
  have hφ : (φ₀.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp φ₀.toMonoidHom := MonoidHom.ext fun _ => rfl
  rw [hφ, ← Subgroup.map_map, hgU]

private theorem utri_eq_upperUnipotent' (F : Type) [Field F] :
    CFSG.CGT.Timmesfeld75.utri F = upperUnipotent F := by
  ext g
  rw [CFSG.CGT.Timmesfeld75.mem_utri_iff, mem_upperUnipotent_iff F]
  have e : ∀ s : F, CFSG.CGT.Timmesfeld75.utriElt s = upperElt F s := fun s =>
    CFSG.CGT.Timmesfeld75.sl2_ext (by simp [CFSG.CGT.Timmesfeld75.utriElt_apply_00, upperElt])
      (by simp [CFSG.CGT.Timmesfeld75.utriElt_apply_01, upperElt])
      (by simp [CFSG.CGT.Timmesfeld75.utriElt_apply_10, upperElt])
      (by simp [CFSG.CGT.Timmesfeld75.utriElt_apply_11, upperElt])
  simp only [e]

theorem exists_normal_mulEquiv_SL2_of_isTI {X : Type} [Group X]
    [Finite X] (B : Sylow 2 X) {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card (B : Subgroup X) = 2 ^ n)
    (hexp : ∀ a ∈ (B : Subgroup X), a * a = 1) (hTI : fusionIsTI (B : Subgroup X))
    (hne : Subgroup.normalizer ((B : Subgroup X) : Set X) ≠ ⊤) :
    ∃ Y : Subgroup X, Y.Normal ∧ (B : Subgroup X) ≤ Y ∧
      ∃ φ : ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        ((B : Subgroup X).subgroupOf Y).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
        ∀ g : X, (B : Subgroup X).map (MulAut.conj g).toMonoidHom ≠ (B : Subgroup X) →
          (B : Subgroup X) ⊔ (B : Subgroup X).map (MulAut.conj g).toMonoidHom = Y := by
  classical
  set S : Set X := {x | x * x = 1} with hS
  set Y : Subgroup X := Subgroup.closure S with hY
  have hBY : (B : Subgroup X) ≤ Y := fun b hb => Subgroup.subset_closure (hexp b hb)
  have hconjY : ∀ g : X, ∀ x ∈ Y, g * x * g⁻¹ ∈ Y := by
    intro g x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      show (g * x * g⁻¹) * (g * x * g⁻¹) = 1
      have hxx : x * x = 1 := hx
      calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hxx]; group
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact Y.mul_mem hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact Y.inv_mem hx
  have hYn : Y.Normal := ⟨fun x hx g => hconjY g x hx⟩
  have hBgY : ∀ g : X, (B : Subgroup X).map (MulAut.conj g).toMonoidHom ≤ Y := by
    rintro g _ ⟨b, hb, rfl⟩
    exact hconjY g b (hBY hb)
  have hBp : IsPGroup 2 ((B : Subgroup X).subgroupOf Y) := B.isPGroup'.comap_subtype
  have hBi : ¬ 2 ∣ ((B : Subgroup X).subgroupOf Y).index := fun h =>
    B.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hBY))
  let PY : Sylow 2 ↥Y := hBp.toSylow hBi
  have hPY : (PY : Subgroup ↥Y) = (B : Subgroup X).subgroupOf Y := IsPGroup.toSylow_coe hBp hBi
  have hcardY : Nat.card (PY : Subgroup ↥Y) = 2 ^ n := by
    rw [hPY, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv
  have hexpY : ∀ a ∈ (PY : Subgroup ↥Y), a * a = 1 := by
    intro a ha
    rw [hPY] at ha
    exact Subtype.ext (hexp a ha)
  have hTIY : fusionIsTI (PY : Subgroup ↥Y) := by
    intro y hy
    rw [hPY] at hy ⊢
    have hne' : (B : Subgroup X).map (MulAut.conj (y : X)).toMonoidHom ≠ B := fun h =>
      hy ((CFSG.Timmesfeld.Bridge.map_conj_subgroupOf_eq_self_iff hBY y).2 h)
    have hbot := hTI (y : X) hne'
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hz1' : (z : X) ∈ (B : Subgroup X) := hz1
    have hz2' : (z : X) ∈ (B : Subgroup X).map (MulAut.conj (y : X)).toMonoidHom := by
      rw [← CFSG.Timmesfeld.Bridge.map_subtype_map_conj_subgroupOf hBY y]
      exact ⟨z, hz2, rfl⟩
    have hz3 : (z : X) ∈ (B : Subgroup X) ⊓
        (B : Subgroup X).map (MulAut.conj (y : X)).toMonoidHom := ⟨hz1', hz2'⟩
    rw [hbot, Subgroup.mem_bot] at hz3
    exact Subtype.ext hz3
  have hgenY : ∀ N' : Subgroup ↥Y, (∀ y : ↥Y, y * y = 1 → y ∈ N') → N' = ⊤ := by
    intro N' hN'
    rw [eq_top_iff]
    intro y _
    have hle : Y ≤ N'.map Y.subtype := by
      refine (Subgroup.closure_le _).2 ?_
      intro s hs
      exact ⟨⟨s, Subgroup.subset_closure hs⟩, hN' _ (Subtype.ext hs), rfl⟩
    obtain ⟨y', hy', hyy⟩ := hle y.2
    have hyy' : y' = y := Subtype.ext hyy
    rwa [hyy'] at hy'
  have hgp : ∀ g : X,
      IsPGroup 2 (((B : Subgroup X).map (MulAut.conj g).toMonoidHom).subgroupOf Y) :=
    fun g => (B.isPGroup'.map _).comap_subtype
  have hgi : ∀ g : X,
      ¬ 2 ∣ (((B : Subgroup X).map (MulAut.conj g).toMonoidHom).subgroupOf Y).index := by
    intro g h
    apply B.not_dvd_index
    have h1 := h.trans (Subgroup.relIndex_dvd_index_of_le (hBgY g))
    rwa [show ((B : Subgroup X).map (MulAut.conj g).toMonoidHom).index =
      (B : Subgroup X).index from Subgroup.index_map_equiv _ (MulAut.conj g)] at h1
  let Qg : X → Sylow 2 ↥Y := fun g => (hgp g).toSylow (hgi g)
  have hQg : ∀ g : X, (Qg g : Subgroup ↥Y) =
      ((B : Subgroup X).map (MulAut.conj g).toMonoidHom).subgroupOf Y :=
    fun g => IsPGroup.toSylow_coe (hgp g) (hgi g)
  have hQeq : ∀ g : X, Qg g = PY → (B : Subgroup X).map (MulAut.conj g).toMonoidHom = B := by
    intro g h
    have h2 : ((B : Subgroup X).map (MulAut.conj g).toMonoidHom).subgroupOf Y =
        (B : Subgroup X).subgroupOf Y := by
      rw [← hQg g, ← hPY, h]
    have h3 := congrArg (Subgroup.map Y.subtype) h2
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (hBgY g), inf_eq_left.2 hBY] at h3
    exact h3
  have hneY : Subgroup.normalizer ((PY : Subgroup ↥Y) : Set ↥Y) ≠ ⊤ := by
    intro htop
    apply hne
    have hnormal : (PY : Subgroup ↥Y).Normal := Subgroup.normalizer_eq_top_iff.1 htop
    have : Unique (Sylow 2 ↥Y) := Sylow.unique_of_normal PY hnormal
    rw [Subgroup.normalizer_eq_top_iff]
    refine ⟨fun x hx g => ?_⟩
    have hBg := hQeq g (Subsingleton.elim _ _)
    have : g * x * g⁻¹ ∈ (B : Subgroup X).map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, rfl⟩
    rwa [hBg] at this
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_SL2_of_isTI PY hn hcardY hexpY hTIY hneY hgenY
  have hφ' : ((B : Subgroup X).subgroupOf Y).map φ.toMonoidHom =
      upperUnipotent (GaloisField 2 n) := by
    rw [← hPY]
    exact hφ
  refine ⟨Y, hYn, hBY, φ, hφ', ?_⟩
  intro g hg
  have hL2 : CFSG.CGT.Timmesfeld75.IsL2Pair ↥Y (PY : Subgroup ↥Y) (2 ^ n) := by
    refine ⟨GaloisField 2 n, inferInstance, inferInstance, inferInstance, φ,
      GaloisField.card 2 n (by omega), ?_⟩
    rw [hPY, hφ', utri_eq_upperUnipotent']
  have hPQ : PY ≠ Qg g := fun h => hg (hQeq g h.symm)
  have htop := hL2.sup_sylow_eq_top hPQ
  have h4 := congrArg (Subgroup.map Y.subtype) htop
  rw [Subgroup.map_sup, hPY, hQg g, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hBY, inf_eq_left.2 (hBgY g),
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h4
  exact h4

end CFSG.CGT.PushingUpLit.C2L

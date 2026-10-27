module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.CGT.PushingUpLit.A78.BenderTIBender

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG CFSG.Open Subgroup
open scoped MatrixGroups

section Core

variable {X : Type} [Group X] [Finite X]

theorem inf_eq_bot_of_two_group_of_odd {A B : Subgroup X} (hA : IsPGroup 2 A)
    (hB : Odd (Nat.card B)) : A ⊓ B = ⊥ := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have h1 : Nat.card ↥(A ⊓ B) ∣ 2 ^ n := hn ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(A ⊓ B) ∣ Nat.card B := Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (2 ^ n) (Nat.card B) := Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hB)
  exact Subgroup.card_eq_one.mp ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)

omit [Finite X] in
theorem mem_normalizer_of_commute_of_ti {Z : Subgroup X} (hTI : fusionIsTI Z) {a m : X}
    (ha : a ∈ Z) (ha1 : a ≠ 1) (hm : m * a = a * m) : m ∈ normalizer (Z : Set X) := by
  by_contra hmn
  have hconj : Z.map (MulAut.conj m).toMonoidHom ≠ Z := fun h =>
    hmn (mem_normalizer_of_map_conj_eq h)
  have hbot := hTI m hconj
  have : a ∈ Z ⊓ Z.map (MulAut.conj m).toMonoidHom :=
    ⟨ha, ⟨a, ha, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hm]
      group⟩⟩
  rw [hbot] at this
  exact ha1 (Subgroup.mem_bot.mp this)

theorem centralizes_of_ti {Z M : Subgroup X} [M.Normal] (hZ : IsElemAbelian 2 Z)
    (h4 : 4 ≤ Nat.card Z) (hTI : fusionIsTI Z) (hM : Odd (Nat.card M)) :
    ∀ m ∈ M, ∀ z ∈ Z, m * z = z * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZN : Z ≤ normalizer (M : Set X) := by
    rw [(Subgroup.normalizer_eq_top_iff).mpr inferInstance]
    exact le_top
  let _ : MulDistribMulAction Z M :=
    MulDistribMulAction.compHom M (M.normalizerMonoidHom.comp (Subgroup.inclusion hZN))
  have hZp : IsPGroup 2 Z := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa [pow_two] using hZ.2 x x.2)⟩
  have : Fact (IsPGroup 2 Z) := ⟨hZp⟩
  let _ : CommGroup Z :=
    { (inferInstance : Group Z) with mul_comm := fun a b => hZ.1.is_comm.comm a b }
  have hncyc : ¬ IsCyclic Z := by
    intro hcyc
    obtain ⟨c, hc⟩ := hcyc.exists_generator
    have h1 : orderOf c = Nat.card Z := orderOf_eq_card_of_forall_mem_zpowers hc
    have h2 : orderOf c ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hZ.2 c c.2))
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have htop := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := M) (A := Z) 2 (Nat.coprime_two_left.2 hM) hncyc
  have hle : (⨆ (a : Z) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) M) ≤
      (normalizer (Z : Set X)).comap M.subtype := by
    refine iSup₂_le fun a ha1 m hm => ?_
    rw [FixedPoints.mem_subgroup] at hm
    have h2 : (a : X) * m * (a : X)⁻¹ = m :=
      congrArg Subtype.val (hm ⟨a, Subgroup.mem_zpowers a⟩)
    have h3 : (m : X) * a = a * m := by
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    exact mem_normalizer_of_commute_of_ti hTI a.2 (fun h => ha1 (Subtype.ext h)) h3
  have hMN : M ≤ normalizer (Z : Set X) := by
    intro m hm
    have : (⟨m, hm⟩ : M) ∈ (normalizer (Z : Set X)).comap M.subtype :=
      hle (htop ▸ Subgroup.mem_top _)
    exact this
  have hZM : Z ⊓ M = ⊥ := inf_eq_bot_of_two_group_of_odd hZp hM
  intro m hm z hz
  have h1 : m * z * m⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hMN hm) z).mp hz
  have hc1 : m * z * m⁻¹ * z⁻¹ ∈ Z := Z.mul_mem h1 (Z.inv_mem hz)
  have hc2 : m * z * m⁻¹ * z⁻¹ ∈ M := by
    have : m * (z * m⁻¹ * z⁻¹) ∈ M :=
      M.mul_mem hm (Normal.conj_mem inferInstance _ (M.inv_mem hm) z)
    simpa [mul_assoc] using this
  have hc : m * z * m⁻¹ * z⁻¹ = 1 := by
    have : m * z * m⁻¹ * z⁻¹ ∈ Z ⊓ M := ⟨hc1, hc2⟩
    rw [hZM] at this
    exact Subgroup.mem_bot.mp this
  calc m * z = (m * z * m⁻¹ * z⁻¹) * z * m := by group
    _ = z * m := by rw [hc, one_mul]

theorem exists_mem_conj_of_two_element (S : Sylow 2 X) {d : X} (hd : ∃ k : ℕ, d ^ 2 ^ k = 1) :
    ∃ x : X, d ∈ (S : Subgroup X).map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hp : IsPGroup 2 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨P, hdP⟩ := hp.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X S P
  refine ⟨x, ?_⟩
  have := congrArg Sylow.toSubgroup hx
  rw [Sylow.coe_subgroup_smul] at this
  have hP : (P : Subgroup X) = (S : Subgroup X).map (MulAut.conj x).toMonoidHom := this.symm
  rw [← hP]
  exact hdP (Subgroup.mem_zpowers d)

theorem centralizes_two_element {M : Subgroup X} [M.Normal] (S : Sylow 2 X)
    (hc : ∀ m ∈ M, ∀ z ∈ (S : Subgroup X), m * z = z * m) :
    ∀ m ∈ M, ∀ d : X, (∃ k : ℕ, d ^ 2 ^ k = 1) → m * d = d * m := by
  intro m hm d hd
  obtain ⟨x, z, hz, rfl⟩ := exists_mem_conj_of_two_element S hd
  have hm' : x⁻¹ * m * x ∈ M := by
    have := Normal.conj_mem (inferInstance : M.Normal) m hm x⁻¹
    simpa using this
  have h := hc (x⁻¹ * m * x) hm' z hz
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc m * (x * z * x⁻¹) = x * ((x⁻¹ * m * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * m * x)) * x⁻¹ := by rw [h]
    _ = (x * z * x⁻¹) * m := by group

omit [Finite X] in
theorem normal_closure_two_elements :
    (Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    refine Subgroup.subset_closure ⟨k, ?_⟩
    rw [conj_pow, hk]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

omit [Finite X] in
theorem le_of_simple_of_normal {I Z D : Subgroup X} [IsSimpleGroup I] [D.Normal] (hZD : Z ≤ D)
    (hZI : Z ≤ I) (hZ1 : Z ≠ ⊥) : I ≤ D := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.subgroupOf I) with h | h
  · exfalso
    apply hZ1
    have h1 : Disjoint D I := Subgroup.subgroupOf_eq_bot.mp h
    exact eq_bot_iff.mpr fun z hz => h1.le_bot ⟨hZD hz, hZI hz⟩
  · exact Subgroup.subgroupOf_eq_top.mp h

theorem SL2_not_comm (K : Type*) [Field K] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
  refine ⟨CFSG.Timmesfeld.RankOne.upperElt K 1, CFSG.Timmesfeld.RankOne.lowerElt K 1, fun h => ?_⟩
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  simp [CFSG.Timmesfeld.RankOne.upperElt, CFSG.Timmesfeld.RankOne.lowerElt, Matrix.mul_apply,
    Fin.sum_univ_two] at this

theorem isSimpleGroup_SL2_charTwo (K : Type*) [Field K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (CFSG.Timmesfeld.RankOne.psl2EquivSL2 K).symm.isSimpleGroup

theorem oTwoPrime_eq_of_tiSylow_core (S : Sylow 2 X) {I : Subgroup X}
    {e : ℕ} (he : 2 ≤ e) (hZ : IsElemAbelian 2 (S : Subgroup X))
    (hZcard : Nat.card (S : Subgroup X) = 2 ^ e) (hTI : fusionIsTI (S : Subgroup X))
    (hZI : (S : Subgroup X) ≤ I) (hI : Nonempty (I ≃* Matrix.SpecialLinearGroup (Fin 2)
      (GaloisField 2 e))) :
    Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1} = I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hI
  set Z : Subgroup X := (S : Subgroup X) with hZdef
  have hZexp : ∀ x ∈ Z, x * x = 1 := fun x hx => by simpa [pow_two] using hZ.2 x hx
  have hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hZ.1.is_comm.comm (⟨x, hx⟩ : Z) ⟨y, hy⟩)
  have h4 : 4 ≤ 2 ^ e :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hZ1 : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard
    omega
  have hZp : IsPGroup 2 Z := S.isPGroup'
  have hF : Nat.card (GaloisField 2 e) = 2 ^ e := GaloisField.card 2 e (by omega)
  have hSLs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) :=
    isSimpleGroup_SL2_charTwo _ (by rw [hF]; exact h4)
  have hIs : IsSimpleGroup I := φ.isSimpleGroup
  have hInc : ∃ a b : I, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := SL2_not_comm (GaloisField 2 e)
    exact ⟨φ.symm a, φ.symm b, fun h => hab (by simpa using congrArg φ h)⟩
  have hnn : ¬ Z.Normal := by
    intro hN
    have : (Z.subgroupOf I).Normal := Normal.subgroupOf hN I
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Z.subgroupOf I) with h | h
    · exact hZ1 ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hZI)
    · have hIZ : I ≤ Z := Subgroup.subgroupOf_eq_top.mp h
      obtain ⟨a, b, hab⟩ := hInc
      exact hab (Subtype.ext (hZab _ (hIZ a.2) _ (hIZ b.2)))
  have hSE := fusionStronglyEmbedded_normalizer_of_ti S hTI hZ1 hnn
  obtain ⟨M, N, hMn, hNn, hMN, hModd, hNodd, hcardN⟩ :=
    exists_odd_normal_series S he hZexp hZab hZcard hSE
  set D : Subgroup X := Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1} with hD
  have hDn : D.Normal := normal_closure_two_elements
  have hZD : Z ≤ D := fun z hz => Subgroup.subset_closure ⟨1, by simpa [pow_two] using hZexp z hz⟩
  have hID : I ≤ D := le_of_simple_of_normal hZD hZI hZ1
  have hZN : Z ≤ N := fun z hz =>
    mem_of_two_pow_of_odd_index N hNodd ⟨1, by simpa [pow_two] using hZexp z hz⟩
  have hIN : I ≤ N := le_of_simple_of_normal hZN hZI hZ1
  have hIM : I ⊓ M = ⊥ := by
    have : (M.subgroupOf I).Normal := Normal.subgroupOf hMn I
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf I) with h | h
    · exact (Subgroup.subgroupOf_eq_bot.mp h).symm.eq_bot
    · exfalso
      have hIM' : I ≤ M := Subgroup.subgroupOf_eq_top.mp h
      have : Z ⊓ M = ⊥ := inf_eq_bot_of_two_group_of_odd hZp hModd
      exact hZ1 (by rw [← this]; exact (inf_eq_left.mpr (hZI.trans hIM')).symm)
  have hNIM : ∀ n ∈ N, ∃ i ∈ I, ∃ m ∈ M, n = i * m := by
    set M' : Subgroup N := M.subgroupOf N with hM'
    have : M'.Normal := Normal.subgroupOf hMn N
    let ψ : I →* N ⧸ M' := (QuotientGroup.mk' M').comp (Subgroup.inclusion hIN)
    have hψinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro i hi
      have h1 : Subgroup.inclusion hIN i ∈ M' := (QuotientGroup.eq_one_iff _).mp hi
      have h2 : (i : X) ∈ M := Subgroup.mem_subgroupOf.mp h1
      have : (i : X) ∈ I ⊓ M := ⟨i.2, h2⟩
      rw [hIM] at this
      exact Subtype.ext (Subgroup.mem_bot.mp this)
    have hM'card : Nat.card M' = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv
    have hquot : Nat.card (N ⧸ M') = Nat.card (Matrix.SpecialLinearGroup (Fin 2)
        (GaloisField 2 e)) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M'
      rw [hM'card, hcardN, mul_comm] at h1
      exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
    have hbij : Function.Bijective ψ :=
      hψinj.bijective_of_nat_card_le (by rw [hquot, Nat.card_congr φ.toEquiv])
    intro n hn
    obtain ⟨i, hi⟩ := hbij.2 (QuotientGroup.mk ⟨n, hn⟩)
    have h1 : (Subgroup.inclusion hIN i)⁻¹ * ⟨n, hn⟩ ∈ M' := by
      rw [← QuotientGroup.eq]
      exact hi
    have h2 : (i : X)⁻¹ * n ∈ M := Subgroup.mem_subgroupOf.mp h1
    exact ⟨i, i.2, _, h2, by group⟩
  have hMZ := centralizes_of_ti (M := M) hZ (by rw [hZcard]; exact h4) hTI hModd
  have hM2 := centralizes_two_element (M := M) S hMZ
  have hMD : ∀ m ∈ M, ∀ y ∈ D, m * y = y * m := by
    intro m hm y hy
    have hle : D ≤ Subgroup.centralizer ({m} : Set X) := by
      refine (Subgroup.closure_le _).mpr fun d hd => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hM2 m hm d hd).symm
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    exact this.symm
  have h2el : ∀ d : X, (∃ k : ℕ, d ^ 2 ^ k = 1) → d ∈ I := by
    intro d hd
    have hdN : d ∈ N := mem_of_two_pow_of_odd_index N hNodd hd
    obtain ⟨i, hi, m, hm, rfl⟩ := hNIM d hdN
    obtain ⟨k, hk⟩ := hd
    have hmi : Commute i m := (hMD m hm i (hID hi)).symm
    have h1 : i ^ 2 ^ k * m ^ 2 ^ k = 1 := by rw [← hmi.mul_pow]; exact hk
    have h2 : m ^ 2 ^ k = (i ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : m ^ 2 ^ k ∈ I ⊓ M :=
      ⟨by rw [h2]; exact I.inv_mem (I.pow_mem hi _), M.pow_mem hm _⟩
    rw [hIM] at h3
    have h4 : m ^ 2 ^ k = 1 := Subgroup.mem_bot.mp h3
    have hord : orderOf m ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h4
    have hodd : orderOf m ∣ Nat.card M := by
      rw [← Subgroup.orderOf_mk m hm]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) (Nat.card M) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hModd)
    have h5 : orderOf m = 1 := (hcop.coprime_dvd_left hord).eq_one_of_dvd hodd
    have hm1 : m = 1 := orderOf_eq_one_iff.mp h5
    rw [hm1, mul_one]
    exact hi
  exact le_antisymm ((Subgroup.closure_le I).mpr h2el) hID

end Core

section Wrapper

variable {G : Type} [Group G]

omit [Group G] in
theorem map_conj_subgroupOf_eq [Group G] {H Z : Subgroup G} (g : H) :
    (Z.subgroupOf H).map (MulAut.conj g).toMonoidHom =
      (Z.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf H := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    have hz' : (g : G)⁻¹ * (x : G) * g = z := by rw [← hzx]; group
    refine ⟨(g⁻¹ * x * g : H), ?_, ?_⟩
    · have : (((g⁻¹ * x * g : H)) : G) = z := by
        rw [← hz']
        simp
      rw [this]
      exact hz
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group

theorem oTwoPrime_eq_of_tiSylow [Finite G] {H Z I : Subgroup G}
    {e : ℕ} (he : 2 ≤ e) (hZ : IsElemAbelian 2 Z) (hZcard : Nat.card Z = 2 ^ e)
    (hZsyl : CFSG.ABGLocalTools.IsSylowOf 2 Z H) (hTI : fusionIsTI Z) (hIH : I ≤ H)
    (hZI : Z ≤ I) (hI : Nonempty (I ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e))) :
    Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} = I := by
  obtain ⟨Q, hQ⟩ := hZsyl
  have hZH : Z ≤ H := hQ ▸ Subgroup.map_subtype_le _
  have hQZ : (Q : Subgroup H) = Z.subgroupOf H := by
    rw [← hQ]
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hZ' : IsElemAbelian 2 (Q : Subgroup H) := by
    rw [hQZ]
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have h := hZ.1.is_comm.comm (⟨((a : H) : G), a.2⟩ : Z) ⟨((b : H) : G), b.2⟩
      have h' : ((a : H) : G) * ((b : H) : G) = ((b : H) : G) * ((a : H) : G) :=
        congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    · exact Subtype.ext (by simpa using hZ.2 (x : G) (Subgroup.mem_subgroupOf.mp hx))
  have hcard' : Nat.card (Q : Subgroup H) = 2 ^ e := by
    rw [hQZ]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv).trans hZcard
  have hTI' : fusionIsTI (Q : Subgroup H) := by
    rw [hQZ]
    intro g hg
    rw [map_conj_subgroupOf_eq] at hg ⊢
    have hne : Z.map (MulAut.conj (g : G)).toMonoidHom ≠ Z := fun h => hg (by rw [h])
    have hbot := hTI (g : G) hne
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : (x : G) ∈ Z ⊓ Z.map (MulAut.conj (g : G)).toMonoidHom := ⟨hx1, hx2⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
  have hZI' : (Q : Subgroup H) ≤ I.subgroupOf H := by
    rw [hQZ]
    intro x hx
    exact hZI hx
  have hI' : Nonempty (↥(I.subgroupOf H) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) :=
    hI.map fun φ => (Subgroup.subgroupOfEquivOfLe hIH).trans φ
  have hcore := oTwoPrime_eq_of_tiSylow_core (X := H) Q he hZ' hcard' hTI' hZI' hI'
  have h1 := congrArg (Subgroup.map H.subtype) hcore
  rw [MonoidHom.map_closure, Subgroup.subgroupOf_map_subtype, inf_of_le_left hIH] at h1
  rw [← h1]
  congr 1
  ext g
  constructor
  · rintro ⟨hg, k, hk⟩
    exact ⟨⟨g, hg⟩, ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨x.2, k, by simpa using congrArg Subtype.val hk⟩

end Wrapper

end CFSG.CGT.PushingUpLit.A78

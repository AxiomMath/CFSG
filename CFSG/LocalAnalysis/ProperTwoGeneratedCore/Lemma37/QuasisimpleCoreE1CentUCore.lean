module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv

theorem le_of_central_isPGroup {G : Type*} [Group G] [Finite G]
    (hG : CFSG.pPrimeCore 2 G = ⊥) {N P : Subgroup G} [N.Normal] (hP : IsPGroup 2 P)
    (hcomm : ∀ n ∈ N, ∀ p ∈ P, n * p = p * n)
    (hall : ∀ n ∈ N, (∃ k : ℕ, n ^ 2 ^ k = 1) → n ∈ P) : N ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' : Sylow 2 N :=
    { toSubgroup := P.subgroupOf N
      isPGroup' := hP.comap_subtype
      is_maximal' := fun {R} hR hPR => le_antisymm (fun r hr => by
        obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
        have hk' : (r : G) ^ 2 ^ k = 1 := by
          simpa using congrArg (fun w : R => ((w : N) : G)) hk
        exact Subgroup.mem_subgroupOf.mpr (hall r r.2 ⟨k, hk'⟩)) hPR }
  have hP' : Subgroup.normalizer (P' : Set N) ≤ Subgroup.centralizer (P' : Set N) := fun n _ =>
    Subgroup.mem_centralizer_iff.mpr fun p hp => Subtype.ext
      (hcomm n n.2 p (Subgroup.mem_subgroupOf.mp hp)).symm
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P' hP'
  have hodd := MonoidHom.not_dvd_card_ker_transferSylow P' hP'
  have hle : (MonoidHom.transferSylow P' hP').ker ≤ CFSG.pPrimeCore 2 N :=
    le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd⟩
  have hbot : (MonoidHom.transferSylow P' hP').ker = ⊥ := by
    have h1 := (Subgroup.map_mono (f := N.subtype) hle).trans
      (CFSG.pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 N)
    rw [hG, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at h1
    exact h1
  rw [hbot, Subgroup.isComplement'_bot_left] at hcompl
  intro n hn
  have hmem : (⟨n, hn⟩ : N) ∈ (P' : Subgroup N) := by
    rw [hcompl]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem centralElt_mem_sylow :
    (⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩ : quasiNormalizer u) ∈
      (T : Subgroup (quasiNormalizer u)) :=
  mem_sylow_of_mem_partCSylow (partCRight_le d.caseC3BCD.partC.mem_right)

theorem quasiSelf_mem_sylow : quasiSelf u ∈ (T : Subgroup (quasiNormalizer u)) :=
  mem_sylow_of_mem_partCSylow (partCRight_le d.caseC3BCD.partC.self_mem)

theorem m_ne : m ≠ 1 ∧ m ≠ centralElt J ∧ m ≠ u ∧ m ≠ u * centralElt J := by
  have hc := d.caseC3BCD.partC
  obtain ⟨hu1, hm1, hum1⟩ := d.caseC3BCD.mk_ne_one
  have hmk : ∀ g : J, (g : J ⧸ Subgroup.center J) = 1 ↔ g = 1 ∨ g = centralElt J := fun g => by
    rw [QuotientGroup.eq_one_iff, d.setting.mem_center_iff]
  refine ⟨fun h => hm1 ((hmk m).mpr (Or.inl h)), fun h => hm1 ((hmk m).mpr (Or.inr h)),
    fun h => hum1 ?_, fun h => hum1 ?_⟩
  · rw [h, ← QuotientGroup.mk_mul, hc.sq]
    exact (hmk _).mpr (Or.inr rfl)
  · rw [h, ← QuotientGroup.mk_mul, show u * (u * centralElt J) = u * u * centralElt J by group,
      hc.sq, hc.centralElt_mul_self]
    exact QuotientGroup.mk_one _

theorem m_mul_self : m * m = centralElt J := by
  obtain ⟨φ⟩ := d.caseC3BCD.quaternion_right
  have hc := d.caseC3BCD.partC
  obtain ⟨h1, he, -, -⟩ := d.m_ne
  exact quaternion_mul_self_of_ne φ hc.mem_right hc.order d.caseC3BCD.m_mem h1 he

theorem mem_right_cases {p : J} (hp : p ∈ partCRight T L) :
    p = 1 ∨ p = centralElt J ∨ p = u ∨ p = u * centralElt J ∨ p = m ∨ p = m * centralElt J ∨
      p = u * m ∨ p = u * m * centralElt J := by
  obtain ⟨φ⟩ := d.caseC3BCD.quaternion_right
  have hc := d.caseC3BCD.partC
  obtain ⟨-, -, hmu, hmue⟩ := d.m_ne
  exact quaternion_enum φ hc.mem_right hc.order hc.self_mem d.caseC3BCD.m_mem hp hc.sq
    d.m_mul_self hmu hmue

theorem eq_of_mem_right_of_commute {a b : J} (ha : a ∈ partCRight T L) (hb : b ∈ partCRight T L)
    (hbb : b * b = centralElt J) (hab : a * b = b * a) :
    a = 1 ∨ a = centralElt J ∨ a = b ∨ a = b * centralElt J := by
  obtain ⟨φ⟩ := d.caseC3BCD.quaternion_right
  have hc := d.caseC3BCD.partC
  rcases quaternion_mul_self φ hc.mem_right hc.order ha with haa | haa
  · rcases quaternion_eq_of_mul_self φ hc.mem_right hc.order ha haa with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_contra hne
    push Not at hne
    have h := quaternion_anticomm φ hc.mem_right hc.order hb ha hbb haa hne.2.2.1 hne.2.2.2
    rw [← hab, left_eq_mul] at h
    exact hc.centralElt_ne_one h

theorem orderOf_quasiBar : orderOf (quasiBar u) = 4 :=
  d.starLift.toEscapingLift.orderOf_quasiBar d.setting

omit [Finite J] d in
theorem mem_zpowers_quasiBar {g : QuasiQuotient u}
    (hg : g = 1 ∨ g = quasiCentral u ∨ g = quasiBar u ∨ g = quasiBar u * quasiCentral u) :
    g ∈ Subgroup.zpowers (quasiBar u) := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_zpowers _
  · exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _)
      (Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _))

theorem mem_zpowers_of_isPGroup {c : QuasiQuotient u}
    (hcK : c ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)))
    (hcu : c * quasiBar u = quasiBar u * c) {k : ℕ} (hk : c ^ 2 ^ k = 1) :
    c ∈ Subgroup.zpowers (quasiBar u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn := d.oneComponent.centralizer_normal
  have := zpowers_quasiBar_normal u
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hu2 : IsPGroup 2 (Subgroup.zpowers (quasiBar u)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, d.orderOf_quasiBar]; norm_num)
  obtain ⟨P', hRP'⟩ := (hc2.to_sup_of_normal_right hu2).exists_le_sylow
  set T' := T.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 (quasiNormalizer u)))
  have hT' : (T' : Subgroup (QuasiQuotient u)) =
      (T : Subgroup (quasiNormalizer u)).map (quasiMk u) := Sylow.coe_mapSurjective _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (QuasiQuotient u) T' P'
  have hmemT : ∀ w ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (quasiBar u),
      g⁻¹ * w * g ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) := fun w hw => by
    have h1 := hRP' hw
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hT'] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  have hcT := hmemT c (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have huT := hmemT _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hconjK : ∀ w ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)),
      g⁻¹ * w * g ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) := fun w hw => by
    simpa using hKn.conj_mem w hw g⁻¹
  obtain ⟨a₀, ha₀T, ha₀⟩ := Subgroup.mem_map.mp hcT
  obtain ⟨b₀, hb₀T, hb₀⟩ := Subgroup.mem_map.mp huT
  have ha₀P : (a₀ : J) ∈ partCRight T L := Subgroup.mem_map_of_mem _
    (Subgroup.mem_inf.mpr ⟨ha₀T, Subgroup.mem_comap.mpr (by rw [ha₀]; exact hconjK c hcK)⟩)
  have hb₀P : (b₀ : J) ∈ partCRight T L := Subgroup.mem_map_of_mem _
    (Subgroup.mem_inf.mpr ⟨hb₀T, Subgroup.mem_comap.mpr (by
      rw [hb₀]; exact hconjK _ d.quasiBar_mem_centralizer)⟩)
  have hinj := fun {a b : quasiNormalizer u} (ha : a ∈ (T : Subgroup (quasiNormalizer u)))
    (hb : b ∈ (T : Subgroup (quasiNormalizer u))) (hab : quasiMk u a = quasiMk u b) =>
    quasiMk_injOn_twoGroup u T.isPGroup' ha hb hab
  have hab : a₀ * b₀ = b₀ * a₀ := hinj ((T : Subgroup (quasiNormalizer u)).mul_mem ha₀T hb₀T)
    ((T : Subgroup (quasiNormalizer u)).mul_mem hb₀T ha₀T) (by
      rw [map_mul, map_mul, ha₀, hb₀]
      calc g⁻¹ * c * g * (g⁻¹ * quasiBar u * g) = g⁻¹ * (c * quasiBar u) * g := by group
        _ = g⁻¹ * (quasiBar u * c) * g := by rw [hcu]
        _ = g⁻¹ * quasiBar u * g * (g⁻¹ * c * g) := by group)
  have hbb : b₀ * b₀ = ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩ :=
    hinj ((T : Subgroup (quasiNormalizer u)).mul_mem hb₀T hb₀T) d.centralElt_mem_sylow (by
      rw [map_mul, hb₀, d.quasiMk_centralElt]
      calc g⁻¹ * quasiBar u * g * (g⁻¹ * quasiBar u * g) = g⁻¹ * quasiCentral u * g := by
            simp only [quasiCentral]; group
        _ = quasiCentral u := by rw [d.commute_quasiCentral, inv_mul_cancel_right])
  have hcases := d.eq_of_mem_right_of_commute ha₀P hb₀P (congrArg Subtype.val hbb)
    (congrArg Subtype.val hab)
  have hcg : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
  have hug : quasiBar u = g * (g⁻¹ * quasiBar u * g) * g⁻¹ := by group
  apply mem_zpowers_quasiBar
  rw [hcg, ← ha₀]
  have he₀ := d.quasiMk_centralElt
  rcases hcases with h | h | h | h
  · left
    rw [show a₀ = 1 from Subtype.ext h, map_one, mul_one, mul_inv_cancel]
  · right; left
    rw [show a₀ = ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩ from Subtype.ext h,
      he₀, d.commute_quasiCentral, mul_inv_cancel_right]
  · right; right; left
    rw [show a₀ = b₀ from Subtype.ext h, hb₀, ← hug]
  · right; right; right
    rw [show a₀ = b₀ * ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩ from
      Subtype.ext h, map_mul, hb₀, he₀]
    have hcomm := d.commute_quasiCentral g⁻¹
    calc g * (g⁻¹ * quasiBar u * g * quasiCentral u) * g⁻¹
        = quasiBar u * g * (g⁻¹ * quasiCentral u) := by rw [hcomm]; group
      _ = quasiBar u * quasiCentral u := by group

theorem eq_of_mem_zpowers_quasiBar {g : QuasiQuotient u} (hg : g ∈ Subgroup.zpowers (quasiBar u)) :
    g = 1 ∨ g = quasiCentral u ∨ g = quasiBar u ∨ g = quasiBar u * quasiCentral u := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, d.orderOf_quasiBar]
  have h4 : j % ((4 : ℕ) : ℤ) = 0 ∨ j % ((4 : ℕ) : ℤ) = 1 ∨ j % ((4 : ℕ) : ℤ) = 2 ∨
      j % ((4 : ℕ) : ℤ) = 3 := by omega
  rcases h4 with h | h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero _)
  · exact Or.inr (Or.inr (Or.inl (zpow_one _)))
  · right; left
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
  · right; right; right
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, pow_succ, pow_two, quasiCentral,
      mul_assoc]

theorem mem_zpowers_of_commute {c : QuasiQuotient u}
    (hcK : c ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)))
    (hcu : c * quasiBar u = quasiBar u * c) : c ∈ Subgroup.zpowers (quasiBar u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn := d.oneComponent.centralizer_normal
  have := zpowers_quasiBar_normal u
  set C := Subgroup.centralizer (L : Set (QuasiQuotient u)) ⊓
    Subgroup.centralizer (Subgroup.zpowers (quasiBar u) : Set (QuasiQuotient u)) with hC
  have hu2 : IsPGroup 2 (Subgroup.zpowers (quasiBar u)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, d.orderOf_quasiBar]; norm_num)
  have hcomm : ∀ n ∈ C, ∀ p ∈ Subgroup.zpowers (quasiBar u), n * p = p * n := fun n hn p hp =>
    (Subgroup.mem_centralizer_iff.mp hn.2 p hp).symm
  have hle := le_of_central_isPGroup d.baseConfig.oddCore_eq_bot (N := C) hu2 hcomm
    (fun n hn ⟨k, hk⟩ => d.mem_zpowers_of_isPGroup hn.1
      (hcomm n hn _ (Subgroup.mem_zpowers _)) hk)
  refine hle ⟨hcK, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  exact ((Commute.zpow_left (Commute.symm hcu) j)).eq

theorem quasiBar_mul_mBar : quasiBar u * d.mBar = d.mBar * quasiBar u * quasiCentral u := by
  obtain ⟨φ⟩ := d.caseC3BCD.quaternion_right
  have hc := d.caseC3BCD.partC
  obtain ⟨-, -, hmu, hmue⟩ := d.m_ne
  have h := quaternion_anticomm φ hc.mem_right hc.order hc.self_mem d.caseC3BCD.m_mem hc.sq
    d.m_mul_self hmu hmue
  rw [mBar, ← d.quasiMk_centralElt, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

theorem mBar_mul_self : d.mBar * d.mBar = quasiCentral u := by
  rw [mBar, ← map_mul, ← d.quasiMk_centralElt]
  congr 1
  exact Subtype.ext d.m_mul_self

theorem centralizer_le_sylow :
    Subgroup.centralizer (L : Set (QuasiQuotient u)) ≤
      (T : Subgroup (quasiNormalizer u)).map (quasiMk u) := by
  have := zpowers_quasiBar_normal u
  have hKn := d.oneComponent.centralizer_normal
  have huT : Subgroup.zpowers (quasiBar u) ≤ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ d.quasiSelf_mem_sylow)
  have hmT : d.mBar ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) :=
    Subgroup.mem_map_of_mem _ (mem_sylow_of_mem_partCSylow (partCRight_le d.caseC3BCD.m_mem))
  intro k hk
  have hconj : k * quasiBar u * k⁻¹ ∈ Subgroup.zpowers (quasiBar u) :=
    (inferInstance : (Subgroup.zpowers (quasiBar u)).Normal).conj_mem _ (Subgroup.mem_zpowers _) k
  have hord : orderOf (k * quasiBar u * k⁻¹) = 4 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj k) (quasiBar u)
    rw [MulAut.conj_apply] at h1
    rw [h1, d.orderOf_quasiBar]
  rcases d.eq_of_mem_zpowers_quasiBar hconj with h | h | h | h
  · rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  · rw [h, d.baseConfig.order] at hord
    exact absurd hord (by decide)
  · exact huT (d.mem_zpowers_of_commute hk (by
      calc k * quasiBar u = k * quasiBar u * k⁻¹ * k := by group
        _ = quasiBar u * k := by rw [h]))
  · have hm1 : d.mBar⁻¹ * k ∈ Subgroup.zpowers (quasiBar u) := by
      refine d.mem_zpowers_of_commute
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ d.mBar_mem_centralizer) hk) ?_
      have hku : k * quasiBar u = quasiBar u * quasiCentral u * k := by
        calc k * quasiBar u = k * quasiBar u * k⁻¹ * k := by group
          _ = quasiBar u * quasiCentral u * k := by rw [h]
      have hmu : d.mBar⁻¹ * quasiBar u = quasiBar u * quasiCentral u * d.mBar⁻¹ := by
        have h1 := d.quasiBar_mul_mBar
        calc d.mBar⁻¹ * quasiBar u = d.mBar⁻¹ * (quasiBar u * d.mBar) * d.mBar⁻¹ := by group
          _ = d.mBar⁻¹ * (d.mBar * quasiBar u * quasiCentral u) * d.mBar⁻¹ := by rw [h1]
          _ = quasiBar u * quasiCentral u * d.mBar⁻¹ := by group
      have hee := d.quasiCentral_mul_self
      calc d.mBar⁻¹ * k * quasiBar u = d.mBar⁻¹ * (k * quasiBar u) := by group
        _ = d.mBar⁻¹ * quasiBar u * quasiCentral u * k := by rw [hku]; group
        _ = quasiBar u * quasiCentral u * d.mBar⁻¹ * quasiCentral u * k := by rw [hmu]
        _ = quasiBar u * (quasiCentral u * d.mBar⁻¹ * quasiCentral u) * k := by group
        _ = quasiBar u * (d.mBar⁻¹ * (quasiCentral u * quasiCentral u)) * k := by
          rw [← d.commute_quasiCentral d.mBar⁻¹]; group
        _ = quasiBar u * (d.mBar⁻¹ * k) := by rw [hee]; group
    rw [show k = d.mBar * (d.mBar⁻¹ * k) by group]
    exact Subgroup.mul_mem _ hmT (huT hm1)

theorem mem_centralizer_cases {k : QuasiQuotient u}
    (hk : k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u))) :
    k = 1 ∨ k = quasiCentral u ∨ k = quasiBar u ∨ k = quasiBar u * quasiCentral u ∨
      k = d.mBar ∨ k = d.mBar * quasiCentral u ∨ k = quasiBar u * d.mBar ∨
      k = quasiBar u * d.mBar * quasiCentral u := by
  obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp (d.centralizer_le_sylow hk)
  have htP : (t : J) ∈ partCRight T L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mpr ⟨htT, Subgroup.mem_comap.mpr hk⟩)
  have he := d.quasiMk_centralElt
  set e₀ : quasiNormalizer u := ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩
  set m₀ : quasiNormalizer u := ⟨m, d.m_mem⟩
  rcases d.mem_right_cases htP with h | h | h | h | h | h | h | h
  · exact Or.inl (by rw [show t = 1 from Subtype.ext h, map_one])
  · exact Or.inr (Or.inl (by rw [show t = e₀ from Subtype.ext h, he]))
  · exact Or.inr (Or.inr (Or.inl (by rw [show t = quasiSelf u from Subtype.ext h])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by
      rw [show t = quasiSelf u * e₀ from Subtype.ext h, map_mul, he]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [show t = m₀ from Subtype.ext h]; rfl)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    rw [show t = m₀ * e₀ from Subtype.ext h, map_mul, he]
    rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    rw [show t = quasiSelf u * m₀ from Subtype.ext h, map_mul]
    rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
    rw [show t = quasiSelf u * m₀ * e₀ from Subtype.ext h, map_mul, map_mul, he]
    rfl

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

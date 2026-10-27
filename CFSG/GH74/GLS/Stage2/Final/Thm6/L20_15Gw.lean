module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_15Perf
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.GorensteinWalter CFSG.GH74.GLS.Stage2.Local

theorem le_normalizer_map_subtype' {G : Type} [Group G] (M : Subgroup G) (K : Subgroup M) [K.Normal] :
    M ≤ normalizer ((K.map M.subtype : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, Normal.conj_mem ‹K.Normal› y hy _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨m, hm⟩⁻¹ * y * ⟨m, hm⟩⁻¹⁻¹, Normal.conj_mem ‹K.Normal› y hy _, ?_⟩
    have h1 : (y : G) = m * x * m⁻¹ := hyx
    show (m⁻¹ * (y : G) * m⁻¹⁻¹ : G) = x
    rw [h1]
    group

section Cosets

variable {G : Type} [Group G]

theorem mem_sup_zpowers_cases {J : Subgroup G} {z : G} (hz2 : z * z = 1)
    (hJn : ∀ j ∈ J, z * j * z⁻¹ ∈ J) {b : G} (hb : b ∈ J ⊔ zpowers z) : b ∈ J ∨ b * z ∈ J := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hJn' : ∀ j ∈ J, z⁻¹ * j * z ∈ J := fun j hj => by simpa [hzi] using hJn j hj
  have hconj : ∀ j ∈ J, z * j * z ∈ J := fun j hj => by simpa [hzi] using hJn j hj
  rw [Subgroup.sup_eq_closure] at hb
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
      have hk : z ^ k = z ^ (k % 2) := by
        conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
        rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left; rw [hk, h]; simp
      · right; rw [hk, h]; simp [hz2]
  | one => exact Or.inl J.one_mem
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (J.mul_mem hx hy)
    · right
      have e : x * y * z = x * (y * z) := by group
      rw [e]; exact J.mul_mem hx hy
    · right
      have h1 : z⁻¹ * y * z ∈ J := hJn' y hy
      have e : x * y * z = (x * z) * (z⁻¹ * y * z) := by group
      rw [e]; exact J.mul_mem hx h1
    · left
      have h1 : z * (y * z) * z⁻¹ ∈ J := hJn _ hy
      have e : x * y = (x * z) * (z * (y * z) * z⁻¹) := by
        calc x * y = x * (z * z) * y := by rw [hz2]; group
          _ = (x * z) * (z * (y * z) * z⁻¹) := by group
      rw [e]; exact J.mul_mem hx h1
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (J.inv_mem hx)
    · right
      have h0 : z⁻¹ * x⁻¹ ∈ J := by simpa [mul_inv_rev] using J.inv_mem hx
      have h1 : z * (z⁻¹ * x⁻¹) * z⁻¹ ∈ J := hJn _ h0
      have e : z * (z⁻¹ * x⁻¹) * z⁻¹ = x⁻¹ * z := by
        rw [show z * (z⁻¹ * x⁻¹) * z⁻¹ = x⁻¹ * z⁻¹ by group, hzi]
      rw [e] at h1; exact h1

end Cosets

theorem pPrimeCore_le_of_index_two {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y} (hJi : J.index = 2) :
    pPrimeCore 2 Y ≤ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro o ho
  have hodd : Odd (orderOf o) := by
    have hd : orderOf (⟨o, ho⟩ : ↥(pPrimeCore 2 Y)) ∣ Nat.card ↥(pPrimeCore 2 Y) := orderOf_dvd_natCard _
    have hodd : Odd (Nat.card ↥(pPrimeCore 2 Y)) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := Y))
    have h1 := Odd.of_dvd_nat hodd hd
    rwa [Subgroup.orderOf_mk] at h1
  obtain ⟨k, hk⟩ := hodd
  have hpow : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one o
  have e : o = (o ^ (k + 1)) * (o ^ (k + 1)) := by
    calc o = o * o ^ (2 * k + 1) := by rw [hpow, mul_one]
      _ = o ^ (k + 1) * o ^ (k + 1) := by rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [e]
  exact Subgroup.mul_self_mem_of_index_two hJi _

theorem pgl2_of_isDGroup {Y : Type} [Group Y] [Finite Y] (hD : IsDGroup Y) {J : Subgroup Y}
    (hJn : J.Normal) (hJi : J.index = 2) (hJp : ⁅J, J⁆ = J) {u : Y} (huJ : u ∈ J) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : ∃ r : ℕ, Odd r ∧ IVK.IsPGL2 (Y ⧸ pPrimeCore 2 Y) (fun r' => r' = r) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 Y with hO
  have hOn : O.Normal := pPrimeCore_normal
  have hOJ : O ≤ J := pPrimeCore_le_of_index_two hJi
  let π : Y →* Y ⧸ O := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  set Jb := J.map π with hJb
  have hJbn : Jb.Normal := Subgroup.Normal.map hJn π hπ
  have hJbi : Jb.index = 2 := by
    rw [hJb, Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.mpr hOJ,
      MonoidHom.range_eq_top.mpr hπ, Subgroup.index_top, mul_one]
    exact hJi
  have hJbp : ⁅Jb, Jb⁆ = Jb := by rw [hJb, ← Subgroup.map_commutator, hJp]
  have hJb1 : Jb ≠ ⊥ := by
    intro hbot
    have : u ∈ O := by
      have h1 : π u ∈ Jb := ⟨u, huJ, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff u).mp h1
    have hodd : Odd (orderOf u) := by
      have hd : orderOf (⟨u, this⟩ : ↥O) ∣ Nat.card ↥O := orderOf_dvd_natCard _
      have hodd : Odd (Nat.card ↥O) := Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := Y))
      have h1 := Odd.of_dvd_nat hodd hd
      rwa [Subgroup.orderOf_mk] at h1
    have hord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
    rw [hord] at hodd
    exact absurd hodd (by decide)
  have hJbperf : Group.IsPerfect ↥Jb := Subgroup.isPerfect_iff.mpr hJbp
  have hJbnt : Nontrivial ↥Jb := (Subgroup.nontrivial_iff_ne_bot Jb).mpr hJb1
  cases hD with
  | quotientIsTwoGroup _ hP2 =>
    exfalso
    have hPJ : IsPGroup 2 ↥Jb := hP2.to_subgroup Jb
    exact Group.IsPerfect.not_isNilpotent ↥Jb hPJ.isNilpotent
  | quotientIsASeven _ hA7 =>
    exfalso
    obtain ⟨e⟩ := hA7
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
    have : IsSimpleGroup (Y ⧸ O) := (MulEquiv.isSimpleGroup_congr e).mpr hsimple
    have _hJbn := hJbn
    rcases this.eq_bot_or_eq_top_of_normal Jb with h | h
    · exact hJb1 h
    · rw [h, Subgroup.index_top] at hJbi
      omega
  | quotientHasLinearNormalSubgroup _ K hKp L hLn hLi hLm =>
    let q : (Y ⧸ O) →* (Y ⧸ O) ⧸ L := QuotientGroup.mk' L
    have hsolv : Group.IsSolvable ((Y ⧸ O) ⧸ L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hLi
    have hJq : Jb.map q = ⊥ := by
      by_contra hne
      have hperf' : Group.IsPerfect ↥(Jb.map q) := by
        apply Subgroup.isPerfect_iff.mpr
        rw [← Subgroup.map_commutator, hJbp]
      have hnt : Nontrivial ↥(Jb.map q) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      have := hsolv
      exact Group.IsPerfect.not_isSolvable ↥(Jb.map q) inferInstance
    have hJL : Jb ≤ L := by
      intro x hx
      have h1 : q x ∈ Jb.map q := ⟨x, hx, rfl⟩
      rw [hJq, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff x).mp h1
    have hLtop : L = ⊤ := by
      have hdvd : L.index ∣ Jb.index := Subgroup.index_dvd_of_le hJL
      rw [hJbi] at hdvd
      have : L.index = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact h
        · rw [h] at hLi; exact absurd hLi (by decide)
      exact Subgroup.index_eq_one.mp this
    let e' : (Y ⧸ O) ≃* L := (Subgroup.topEquiv (G := Y ⧸ O)).symm.trans (MulEquiv.subgroupCongr hLtop.symm)
    have hodd : Odd (Nat.card K) := by
      obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hKp
      rw [hcard]; exact hpodd.pow
    rcases hLm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exfalso
      let e'' : (Y ⧸ O) ≃* PSL2 K := e'.trans e
      set J'' := Jb.map e''.toMonoidHom with hJ''
      have hJ''perf : Group.IsPerfect ↥J'' := by
        apply Subgroup.isPerfect_iff.mpr
        rw [hJ'', ← Subgroup.map_commutator, hJbp]
      have hJ''ne : J'' ≠ ⊥ := by
        intro h
        apply hJb1
        have := Subgroup.map_injective (f := e''.toMonoidHom) e''.injective (h.trans (Subgroup.map_bot _).symm)
        exact this
      have hJ''sn : J''.IsSubnormal := by
        have : J''.Normal := Subgroup.Normal.map hJbn e''.toMonoidHom e''.surjective
        exact this.isSubnormal
      have := (psl2_perfect_subnormal_eq_top K hKp J'' hJ''ne hJ''perf hJ''sn).2
      have h2 : Jb = ⊤ := by
        have := Subgroup.map_injective (f := e''.toMonoidHom) e''.injective (this.trans (Subgroup.map_top_of_surjective _ e''.surjective).symm)
        exact this
      rw [h2, Subgroup.index_top] at hJbi
      omega
    · exact ⟨Nat.card K, hodd, K, inferInstance, inferInstance, rfl, ⟨e'.trans e⟩⟩


section GW

variable {G : Type} [Group G] [Finite G]

theorem pgl2_of_dihedral
    {J : Subgroup G} {z : G} (hz2 : z * z = 1) (hzJ : z ∉ J) (hJn : ∀ j ∈ J, z * j * z⁻¹ ∈ J)
    (hJp : ⁅J, J⁆ = J) {u : G} (huJ : u ∈ J) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hdih : ∀ S : Sylow 2 ↥(J ⊔ zpowers z), ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ m))) :
    ∃ r : ℕ, Odd r ∧ PGLModO J (zpowers z) r := by
  set G₁ := J ⊔ zpowers z with hG₁
  have hJG₁ : J ≤ G₁ := le_sup_left
  have hzG₁ : z ∈ G₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hcases : ∀ b ∈ G₁, b ∈ J ∨ b * z ∈ J := fun b hb => mem_sup_zpowers_cases hz2 hJn hb
  have hG₁n : ∀ h ∈ G₁, ∀ j ∈ J, h * j * h⁻¹ ∈ J := by
    intro h hh j hj
    rcases hcases h hh with h1 | h1
    · exact J.mul_mem (J.mul_mem h1 hj) (J.inv_mem h1)
    · have e : h * j * h⁻¹ = (h * z) * (z * j * z⁻¹) * (h * z)⁻¹ := by
        have e1 : (h * z) * (z * j * z⁻¹) * (h * z)⁻¹ = h * (z * z) * j * (z⁻¹ * z⁻¹) * h⁻¹ := by group
        rw [e1, hz2, show z⁻¹ * z⁻¹ = 1 by rw [hzi, hz2]]
        group
      rw [e]
      exact J.mul_mem (J.mul_mem h1 (hJn j hj)) (J.inv_mem h1)
  set J₁ : Subgroup ↥G₁ := J.subgroupOf G₁ with hJ₁
  have hJ₁n : J₁.Normal := ⟨fun n hn g => by
    rw [hJ₁, Subgroup.mem_subgroupOf] at hn ⊢
    exact hG₁n g g.2 n hn⟩
  have hJ₁i : J₁.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨z, hzG₁⟩, fun b => ?_⟩
    have hb := hcases b b.2
    by_cases hbJ : (b : G) ∈ J
    · right
      refine ⟨hbJ, fun h => hzJ ?_⟩
      have h' : (b : G) * z ∈ J := h
      have : z = (b : G)⁻¹ * ((b : G) * z) := by group
      rw [this]; exact J.mul_mem (J.inv_mem hbJ) h'
    · left
      exact ⟨hb.resolve_left hbJ, hbJ⟩
  have hmapJ₁ : J₁.map G₁.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJG₁
  have hJ₁p : ⁅J₁, J₁⁆ = J₁ := by
    apply Subgroup.map_injective G₁.subtype_injective
    rw [Subgroup.map_commutator, hmapJ₁, hJp]
  have hu₁ : u ∈ G₁ := hJG₁ huJ
  set u₁ : ↥G₁ := ⟨u, hu₁⟩ with hu₁def
  have hu₁J : u₁ ∈ J₁ := huJ
  have hu₁2 : u₁ * u₁ = 1 := Subtype.ext hu2
  have hu₁1 : u₁ ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hD : IsDGroup ↥G₁ := gorensteinWalter ↥G₁ hdih
  obtain ⟨r, hr, hpgl⟩ := pgl2_of_isDGroup hD hJ₁n hJ₁i hJ₁p hu₁J hu₁2 hu₁1
  refine ⟨r, hr, ?_⟩
  set B := pPrimeCoreOf 2 J with hB
  have hBJ : B ≤ J := Subgroup.map_subtype_le _
  have hEq : pPrimeCore 2 ↥G₁ = B.subgroupOf G₁ := by
    apply le_antisymm
    · intro o ho
      have hoJ : o ∈ J₁ := pPrimeCore_le_of_index_two hJ₁i ho
      set N : Subgroup G := (pPrimeCore 2 ↥G₁).map G₁.subtype with hN
      have hNJ : N ≤ J := by
        rintro _ ⟨o', ho', rfl⟩
        exact pPrimeCore_le_of_index_two hJ₁i ho'
      have hNnorm : G₁ ≤ normalizer (N : Set G) := le_normalizer_map_subtype' G₁ (pPrimeCore 2 ↥G₁)
      set N' : Subgroup ↥J := N.subgroupOf J with hN'
      have hN'n : N'.Normal := ⟨fun n hn g => by
        rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
        have := (Subgroup.mem_normalizer_iff.mp (hNnorm (hJG₁ g.2)) n).mp hn
        exact this⟩
      have hN'cop : Nat.Coprime 2 (Nat.card N') := by
        have h1 : Nat.card N' = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNJ).toEquiv
        have h2 : Nat.card N = Nat.card (pPrimeCore 2 ↥G₁) :=
          Nat.card_congr (Subgroup.equivMapOfInjective _ G₁.subtype G₁.subtype_injective).symm.toEquiv
        rw [h1, h2]
        exact pPrimeCore_coprime_card
      have hN'le : N' ≤ pPrimeCore 2 ↥J := le_sSup ⟨hN'n, hN'cop⟩
      have hmap : N'.map J.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNJ
      have hNB : N ≤ B := by
        rw [← hmap]; exact Subgroup.map_mono hN'le
      exact hNB ⟨o, ho, rfl⟩
    · have hle : B ≤ pPrimeCoreOf 2 G₁ := pPrimeCoreOf_le_of_normal hJG₁ hG₁n
      intro o ho
      have : (o : G) ∈ pPrimeCoreOf 2 G₁ := hle ho
      obtain ⟨o', ho', hoo⟩ := this
      have : o' = o := Subtype.ext hoo
      rw [← this]; exact ho'
  have hnorm : (B.subgroupOf G₁).Normal := by rw [← hEq]; exact pPrimeCore_normal
  refine ⟨hnorm, ?_⟩
  obtain ⟨F₀, hF₀, hFfin, hP, ⟨e⟩⟩ := hpgl
  refine ⟨F₀, hF₀, hFfin, hP, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hEq.symm).trans e

end GW

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20



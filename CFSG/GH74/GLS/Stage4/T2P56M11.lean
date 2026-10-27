module

public import CFSG.GH74.GLS.Stage4.T2P56Excl
public import CFSG.GH74.GLS.Stage4.T2P56Mat
public import CFSG.GH74.KGroups.M11
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

section M11Facts

def layerM11_equivNative :
    ↥CFSG.Open.StatedM11 ≃* ↥CFSG.Blueprint.NativeSporadic.M11 :=
  MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11

theorem layerM11_isSimple {H : Type} [Group H]
    (e : H ≃* ↥CFSG.Open.StatedM11) : IsSimpleGroup H :=
  e.isSimpleGroup_congr.mpr
    (layerM11_equivNative.isSimpleGroup_congr.mpr CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2)

theorem layerM11_card {H : Type} [Group H]
    (e : H ≃* ↥CFSG.Open.StatedM11) : Nat.card H = 7920 := by
  rw [Nat.card_congr (e.trans layerM11_equivNative).toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M11

theorem layerM11_aut_inner {H : Type} [Group H]
    (e : H ≃* ↥CFSG.Open.StatedM11) (φ : MulAut H) :
    ∃ k : H, ∀ x : H, φ x = k * x * k⁻¹ := by
  have h : CFSG.Blueprint.NativeSporadic.IsSporadic H .M11 := ⟨e.trans layerM11_equivNative⟩
  obtain ⟨M, hP, hA⟩ := CFSG.GH74.KGroups.M11.autModel h
  refine M.inner_of_mem φ ?_
  exact (SetLike.ext_iff.mp (hA.trans hP.symm) _).mp (M.Φ φ).2

theorem layerM11_center_eq_bot {H : Type} [Group H]
    (e : H ≃* ↥CFSG.Open.StatedM11) : Subgroup.center H = ⊥ := by
  have := layerM11_isSimple e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative H := Subgroup.center_eq_top_iff.1 h
    have hp := Group.is_simple_iff_prime_card.1 (layerM11_isSimple e)
    rw [layerM11_card e] at hp
    norm_num at hp

end M11Facts

section Sylow

theorem sylow_center_card_of_sd {H : Type} [Group H] [Finite H] {n : ℕ} (hn : 4 ≤ n)
    (S₀ S : Sylow 2 H) (f : ↥(S₀ : Subgroup H) ≃* CFSG.Open.SemidihedralGroup n) :
    Nat.card (Subgroup.center ↥(S : Subgroup H)) = 2 := by
  obtain ⟨g⟩ := sylow_two_nonempty_mulEquiv S S₀
  have h := CFSG.Semidihedral.center_card n hn
  rw [← Subgroup.map_center_eq (g.trans f),
    Subgroup.card_map_of_injective (g.trans f).injective] at h
  exact h

theorem no_central_four_in_sylow {H : Type} [Group H] [Finite H]
    (hcard : Nat.card H = 7920)
    (hSD : ∃ S : Sylow 2 H, ∃ n : ℕ, 4 ≤ n ∧
      Nonempty (↥(S : Subgroup H) ≃* CFSG.Open.SemidihedralGroup n))
    {Q : Subgroup H} (hQ : Nat.card Q = 8) {m : H} (hm4 : orderOf m = 4)
    (hQm : ∀ q ∈ Q, m * q = q * m) (hmQ : m ∉ Q) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, n, hn, ⟨f⟩⟩ := hSD
  set C : Subgroup H := Subgroup.centralizer ({m} : Set H) with hC
  have hmem : ∀ x : H, x ∈ C ↔ m * x = x * m := by
    intro x
    rw [hC, Subgroup.mem_centralizer_iff]
    simp
  have hQC : Q ≤ C := fun q hq => (hmem q).2 (hQm q hq)
  have hmC : m ∈ C := (hmem m).2 rfl
  set Q' : Subgroup C := Q.subgroupOf C with hQ'
  have hQ'card : Nat.card Q' = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv).trans hQ
  have hQ'p : IsPGroup 2 Q' := IsPGroup.of_card (n := 3) (by rw [hQ'card]; norm_num)
  obtain ⟨S, hQS⟩ := hQ'p.exists_le_sylow
  set m' : C := ⟨m, hmC⟩ with hm'
  have hm'c : m' ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((hmem g.1).1 g.2).symm
  have hm'ord : orderOf m' = 4 := by rw [hm', Subgroup.orderOf_mk, hm4]
  have hzp : IsPGroup 2 (Subgroup.zpowers m') :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hm'ord]; norm_num)
  have hzn : (Subgroup.zpowers m').Normal :=
    Subgroup.normal_of_le_center ((Subgroup.zpowers_le).2 hm'c)
  have hm'S : m' ∈ (S : Subgroup C) := hzp.le_sylow_of_normal S (Subgroup.mem_zpowers m')
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hne : Q' ≠ (S : Subgroup C) := by
    intro h
    apply hmQ
    have : m' ∈ Q' := h ▸ hm'S
    exact this
  have hdvd : Nat.card Q' ∣ Nat.card (S : Subgroup C) := Subgroup.card_dvd_of_le hQS
  have hlt : 8 < 2 ^ k := by
    rw [← hk, ← hQ'card]
    refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun h => hne ?_
    exact Subgroup.eq_of_le_of_card_ge hQS h.symm.le
  have hSdvd : 2 ^ k ∣ 7920 := by
    rw [← hk, ← hcard]
    exact (Subgroup.card_subgroup_dvd_card (S : Subgroup C)).trans
      (Subgroup.card_subgroup_dvd_card C)
  have hk4 : k = 4 := by
    have h1 : k ≤ 4 := by
      by_contra h
      have h2 : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have h3 : 32 ∣ 7920 := h2.trans hSdvd
      omega
    have h2 : 4 ≤ k := by
      by_contra h
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  set S' : Subgroup H := (S : Subgroup C).map C.subtype with hS'
  have hS'card : Nat.card S' = 16 := by
    rw [hS', Subgroup.card_map_of_injective C.subtype_injective, hk, hk4]
    norm_num
  have hS'p : IsPGroup 2 S' := IsPGroup.of_card (n := 4) (by rw [hS'card]; norm_num)
  have hS'idx : ¬ 2 ∣ S'.index := by
    have h1 := Subgroup.card_mul_index S'
    rw [hS'card, hcard] at h1
    have h2 : S'.index = 495 := by omega
    rw [h2]
    norm_num
  set S'' : Sylow 2 H := hS'p.toSylow hS'idx with hS''
  have hS''eq : (S'' : Subgroup H) = S' := IsPGroup.toSylow_coe hS'p hS'idx
  have hcen := sylow_center_card_of_sd hn S₀ S'' f
  have hmS'' : m ∈ (S'' : Subgroup H) := by
    rw [hS''eq]
    exact ⟨m', hm'S, rfl⟩
  have hmz : (⟨m, hmS''⟩ : ↥(S'' : Subgroup H)) ∈ Subgroup.center ↥(S'' : Subgroup H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hg : (g : H) ∈ S' := hS''eq ▸ g.2
    obtain ⟨c, -, hc⟩ := hg
    have : m * (g : H) = (g : H) * m := (hmem g).1 (by rw [← hc]; exact c.2)
    exact this.symm
  have hle : Subgroup.zpowers (⟨m, hmS''⟩ : ↥(S'' : Subgroup H)) ≤
      Subgroup.center ↥(S'' : Subgroup H) := Subgroup.zpowers_le.2 hmz
  have h4 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, Subgroup.orderOf_mk, hm4, hcen] at h4
  omega

end Sylow

section SL2

theorem sl2_three_card {G : Type} [Group G] {K : Subgroup G}
    (hK : HasSL2Model ↥K (fun q => q = 3)) : Nat.card ↥K = 24 := by
  obtain ⟨F, iF, iFin, hF, ⟨e⟩⟩ := hK
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hF]
  norm_num

theorem sl2_central_sq {G : Type} [Group G] {K : Subgroup G} {P : ℕ → Prop}
    (hK : HasSL2Model ↥K P) {c : G} (hc : c ∈ K) (hcc : ∀ k ∈ K, c * k = k * c) :
    c * c = 1 := by
  obtain ⟨F, iF, iFin, hF, ⟨e⟩⟩ := hK
  have hcen : ∀ g : SL2 F, g * e ⟨c, hc⟩ = e ⟨c, hc⟩ * g := by
    intro g
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    apply Subtype.ext
    exact (hcc _ (e.symm g).2).symm
  have h1 : e ⟨c, hc⟩ * e ⟨c, hc⟩ = 1 := by
    rcases sl2s_center hcen with h | h
    · rw [h, mul_one]
    · rw [h, ← map_mul]
      have : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) * (-1) = 1 := by
        ext i j
        simp
      rw [this, map_one]
  have h2 : (⟨c, hc⟩ : ↥K) * ⟨c, hc⟩ = 1 := e.injective (by rw [map_mul, h1, map_one])
  simpa using congrArg Subtype.val h2

theorem exists_card_eight_of_sl2_three {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : HasSL2Model ↥K (fun q => q = 3)) : ∃ Q : Subgroup G, Q ≤ K ∧ Nat.card Q = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : 2 ^ 3 ∣ Nat.card ↥K := by rw [sl2_three_card hK]; norm_num
  obtain ⟨Q₀, hQ₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8
  refine ⟨Q₀.map K.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective, hQ₀]
  norm_num

end SL2

section Core

theorem map_eq_of_simple {G : Type} [Group G] [Finite G] (ψ : MulAut G) (E : Subgroup G) [E.Normal]
    (hsimple : IsSimpleGroup ↥E) {z : G} (hzE : z ∈ E) (hz1 : z ≠ 1) (hψz : ψ z = z) :
    E.map ψ.toMonoidHom = E := by
  have hn : (E.map ψ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance ψ.toMonoidHom ψ.surjective
  have hnn : ((E ⊓ E.map ψ.toMonoidHom).subgroupOf E).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((E ⊓ E.map ψ.toMonoidHom).subgroupOf E) with
    h | h
  · exfalso
    have hz : (⟨z, hzE⟩ : ↥E) ∈ (E ⊓ E.map ψ.toMonoidHom).subgroupOf E := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hzE, ⟨z, hzE, hψz⟩⟩
    rw [h, Subgroup.mem_bot] at hz
    exact hz1 (congrArg Subtype.val hz)
  · have hle : E ≤ E.map ψ.toMonoidHom := fun x hx => by
      have : (⟨x, hx⟩ : ↥E) ∈ (E ⊓ E.map ψ.toMonoidHom).subgroupOf E := h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 this).2
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective ψ.injective])).symm

theorem no_m11_core
    {G : Type} [Group G] [Finite G] (ψ : MulAut G) (E : Subgroup G) [E.Normal]
    (hE : Nonempty (↥E ≃* CFSG.Open.StatedM11))
    (hSD : ∃ S : Sylow 2 ↥E, ∃ n : ℕ, 4 ≤ n ∧
      Nonempty (↥(S : Subgroup ↥E) ≃* CFSG.Open.SemidihedralGroup n))
    {K : Subgroup G} (hKE : K ≤ E) (hK : HasSL2Model ↥K (fun q => q = 3)) {z : G} (hzK : z ∈ K)
    (hz2 : orderOf z = 2) (hψK : ∀ k ∈ K, ψ k = k) (hψ2 : ∀ x, ψ (ψ x) = z * x * z⁻¹) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hE
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hzE : z ∈ E := hKE hzK
  have hsimple : IsSimpleGroup ↥E := layerM11_isSimple e
  have hcardE : Nat.card ↥E = 7920 := layerM11_card e
  have hψE : E.map ψ.toMonoidHom = E := map_eq_of_simple ψ E hsimple hzE hz1 (hψK z hzK)
  let ψE : MulAut ↥E := (ψ.subgroupMap E).trans (MulEquiv.subgroupCongr hψE)
  have hψE_apply : ∀ x : ↥E, ((ψE x : ↥E) : G) = ψ x := fun x => rfl
  obtain ⟨k, hk⟩ := layerM11_aut_inner e ψE
  have hkG : ∀ x : ↥E, ψ x = (k : G) * x * (k : G)⁻¹ := fun x => by
    have := congrArg Subtype.val (hk x)
    rw [hψE_apply] at this
    simpa using this
  set zE : ↥E := ⟨z, hzE⟩ with hzE_def
  have hkk : k * k = zE := by
    have hcen : (k * k)⁻¹ * zE ∈ Subgroup.center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 : ψE (ψE x) = (k * k) * x * (k * k)⁻¹ := by
        rw [hk, hk]
        group
      have h2 : ψE (ψE x) = zE * x * zE⁻¹ := Subtype.ext (hψ2 x)
      rw [h1] at h2
      calc x * ((k * k)⁻¹ * zE) = (k * k)⁻¹ * ((k * k) * x * (k * k)⁻¹) * zE := by group
        _ = (k * k)⁻¹ * (zE * x * zE⁻¹) * zE := by rw [h2]
        _ = ((k * k)⁻¹ * zE) * x := by group
    rw [layerM11_center_eq_bot e, Subgroup.mem_bot] at hcen
    exact inv_mul_eq_one.1 hcen
  have hzEord : orderOf zE = 2 := by rw [hzE_def, Subgroup.orderOf_mk, hz2]
  have hk2 : k ^ 2 = zE := by rw [pow_two]; exact hkk
  have hk4 : orderOf k = 4 := by
    have h1 : ¬ k ^ 2 ^ 1 = 1 := by
      rw [pow_one, hk2]
      intro h
      rw [h, orderOf_one] at hzEord
      omega
    have h2 : k ^ 2 ^ (1 + 1) = 1 := by
      have h3 : k ^ 2 ^ (1 + 1) = (k ^ 2) ^ 2 := by rw [← pow_mul]; norm_num
      rw [h3, hk2]
      have := pow_orderOf_eq_one zE
      rwa [hzEord] at this
    simpa using orderOf_eq_prime_pow h1 h2
  have hkK : ∀ x ∈ K, (k : G) * x = x * (k : G) := by
    intro x hx
    have h : ψ x = (k : G) * x * (k : G)⁻¹ := hkG ⟨x, hKE hx⟩
    rw [hψK x hx] at h
    calc (k : G) * x = ((k : G) * x * (k : G)⁻¹) * (k : G) := by group
      _ = x * (k : G) := by rw [← h]
  have hkNK : (k : G) ∉ K := by
    intro hkK'
    have h1 := sl2_central_sq hK hkK' (fun x hx => hkK x hx)
    have h2 : ((k * k : ↥E) : G) = z := congrArg Subtype.val hkk
    rw [Subgroup.coe_mul] at h2
    exact hz1 (h2 ▸ h1)
  obtain ⟨Q, hQK, hQcard⟩ := exists_card_eight_of_sl2_three hK
  have hQEcard : Nat.card (Q.subgroupOf E) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hQK.trans hKE)).toEquiv).trans hQcard
  refine no_central_four_in_sylow hcardE hSD hQEcard hk4 ?_ ?_
  · intro q hq
    exact Subtype.ext (hkK (q : G) (hQK (Subgroup.mem_subgroupOf.1 hq)))
  · intro hkQ
    exact hkNK (hQK (Subgroup.mem_subgroupOf.1 hkQ))

end Core

section Layer

theorem no_m11_layer
    {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y)
    (E : Subgroup (Y ⧸ CFSG.pPrimeCore 2 Y)) [E.Normal] (hEodd : Odd E.index)
    (hE : Nonempty (↥E ≃* CFSG.Open.StatedM11)) (hSD : HasSDSylow Y)
    {K : Subgroup Y} (hKE : K.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 Y)) ≤ E)
    (hK : HasSL2Model ↥K (fun q => q = 3)) {z : Y} (hzK : z ∈ K)
    (hz2 : orderOf z = 2) (hψK : ∀ k ∈ K, ψ k = k) (hψ2 : ∀ x, ψ (ψ x) = z * x * z⁻¹) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Y := pPrimeCore 2 Y with hN
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := by
    have hcop := pPrimeCore_coprime_card (p := 2) (G := Y)
    rwa [Nat.coprime_two_left] at hcop
  have hP : ∀ q : ℕ, q = 3 → Odd q ∧ 3 ≤ q := by
    intro q hq
    subst hq
    exact ⟨by decide, le_refl _⟩
  have hψN : N.map ψ.toMonoidHom = N := pPrimeCore_map_iso 2 ψ
  let ψb : (Y ⧸ N) ≃* (Y ⧸ N) := QuotientGroup.congr N N ψ hψN
  have hψb : ∀ x : Y, ψb (QuotientGroup.mk' N x) = QuotientGroup.mk' N (ψ x) := fun x => rfl
  have hinj : Set.InjOn (QuotientGroup.mk' N) (K : Set Y) := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.1 hxy
    have h2 : x⁻¹ * y ∈ K := K.mul_mem (K.inv_mem hx) hy
    exact inv_mul_eq_one.1 (eq_one_of_mem_inf_of_sl2 N hNodd hP hK h2 h1)
  have hKb : HasSL2Model ↥(K.map (QuotientGroup.mk' N)) (fun q => q = 3) := by
    obtain ⟨F, iF, iFin, hF, ⟨e⟩⟩ := hK
    exact ⟨F, iF, iFin, hF, ⟨(sdwEquivMapOfInjOn (QuotientGroup.mk' N) K hinj).symm.trans e⟩⟩
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hzN : z ∉ N := fun h => hz1 (eq_one_of_mem_inf_of_sl2 N hNodd hP hK hzK h)
  have hπz : QuotientGroup.mk' N z ≠ 1 := by
    intro h
    apply hzN
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    exact h
  have hz' : orderOf (QuotientGroup.mk' N z) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, ← hz2, pow_orderOf_eq_one, map_one]) hπz
  have hSDE : ∃ S : Sylow 2 ↥E, ∃ n : ℕ, 4 ≤ n ∧
      Nonempty (↥(S : Subgroup ↥E) ≃* CFSG.Open.SemidihedralGroup n) := by
    obtain ⟨S, m, hm, ⟨e⟩⟩ := hSD
    obtain ⟨S', ⟨e'⟩⟩ := exists_sylow_of_layer (T := CFSG.Open.SemidihedralGroup m) ⟨S, ⟨e⟩⟩ E hEodd
    exact ⟨S', m, hm, ⟨e'⟩⟩
  refine no_m11_core ψb E hE hSDE hKE hKb (z := QuotientGroup.mk' N z) ⟨z, hzK, rfl⟩ hz' ?_ ?_
  · rintro _ ⟨k, hk, rfl⟩
    rw [hψb, hψK k hk]
  · intro x'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N x'
    rw [hψb, hψb, hψ2 x]
    simp only [map_mul, map_inv]

end Layer

end CFSG.GH74.GLS.Stage4.Rest

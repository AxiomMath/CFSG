module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasANormalFour
public import CFSG.Assembly.OrderReductions.OddCore
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

open CFSG.ComponentClassification.CentralCover
  (index_two_normal_cyclic_four_central_involution_obstruction)

variable {G : Type*} [Group G]

theorem assembly_oddCore_eq (X : Type*) [Group X] [Finite X] :
    CFSG.Assembly.oddCore X = CFSG.OrderReductions.OddCore.oddCore X := by
  apply le_antisymm
  · exact sSup_le fun N hN => by
      have := hN.1
      exact CFSG.OrderReductions.OddCore.normal_le_oddCore N hN.2
  · exact le_sSup ⟨inferInstance, CFSG.OrderReductions.OddCore.oddCore_odd X⟩

theorem mem_zpowers_of_orderOf_dvd_of_isCyclic [Finite G] {T : Subgroup G} (hT : IsCyclic T)
    {τ u : G} (hτ : τ ∈ T) (hu : u ∈ T) (h : orderOf τ ∣ orderOf u) :
    τ ∈ Subgroup.zpowers u := by
  have hle : Subgroup.zpowers (⟨τ, hτ⟩ : T) ≤ Subgroup.zpowers ⟨u, hu⟩ := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers _))
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem normal_index_le_two_of_mul_mem {H : Subgroup G}
    (h : ∀ a b, a ∉ H → b ∉ H → a * b ∈ H) : H.Normal ∧ H.index ≤ 2 := by
  by_cases htop : H = ⊤
  · subst htop
    exact ⟨inferInstance, by simp⟩
  · obtain ⟨a, ha⟩ : ∃ a, a ∉ H := by
      by_contra hcon
      push Not at hcon
      exact htop (eq_top_iff.mpr fun x _ => hcon x)
    have h2 : H.index = 2 := Subgroup.index_eq_two_iff.mpr ⟨a, fun b => by
      by_cases hb : b ∈ H
      · exact Or.inr ⟨hb, fun hba => ha (by simpa using H.mul_mem (H.inv_mem hb) hba)⟩
      · exact Or.inl ⟨by simpa using h b⁻¹⁻¹ a (by simpa using hb) ha, hb⟩⟩
    exact ⟨Subgroup.normal_of_index_eq_two h2, h2.le⟩

theorem exists_conj_eq_of_mul_self_eq_one [Finite G] {C R : Subgroup G} {t z : G}
    (htC : t ∉ C) (ht : t * t = 1) (htN : t ∈ Subgroup.normalizer (C : Set G))
    (hRC : R ≤ C) (hR : IsPGroup 2 R)
    (hRmax : ∀ P : Subgroup G, P ≤ C → IsPGroup 2 P → Nat.card P ≤ Nat.card R)
    (htR : ∀ r ∈ R, t * r = r * t) (hinv : ∀ w ∈ R, w * w = 1 → w = 1 ∨ w = z)
    {k : G} (hk : k ∈ C) (hj : (t * k) * (t * k) = 1) :
    ∃ c ∈ C, c * (t * k) * c⁻¹ = t ∨ c * (t * k) * c⁻¹ = t * z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htc : ∀ c ∈ C, t * c * t ∈ C := by
    intro c hc
    have := (Subgroup.mem_normalizer_iff.mp htN c).mp hc
    rwa [htinv] at this
  let D : Subgroup G :=
    { carrier := {x | x ∈ C ∨ t * x ∈ C}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (C.mul_mem ha hb)
        · right
          have e : t * (a * b) = (t * a * t) * (t * b) := by
            calc t * (a * b) = t * a * (t * t) * b := by rw [ht, mul_one, mul_assoc]
              _ = (t * a * t) * (t * b) := by group
          rw [e]
          exact C.mul_mem (htc a ha) hb
        · right
          rw [← mul_assoc]
          exact C.mul_mem ha hb
        · left
          have e : a * b = t * (t * a) * t * (t * b) := by
            calc a * b = (t * t) * a * (t * t) * b := by rw [ht, one_mul, mul_one]
              _ = t * (t * a) * t * (t * b) := by group
          rw [e]
          exact C.mul_mem (htc _ ha) hb
      one_mem' := Or.inl C.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (C.inv_mem ha)
        · right
          have e : t * a⁻¹ = t * (t * a)⁻¹ * t := by
            calc t * a⁻¹ = t * a⁻¹ * (t * t) := by rw [ht, mul_one]
              _ = t * (a⁻¹ * t) * t := by group
              _ = t * (t * a)⁻¹ * t := by rw [mul_inv_rev, htinv]
          rw [e]
          exact htc _ (C.inv_mem ha) }
  have hmemD : ∀ x, x ∈ D ↔ x ∈ C ∨ t * x ∈ C := fun x => Iff.rfl
  have hCD : C ≤ D := fun c hc => (hmemD c).mpr (Or.inl hc)
  have htD : t ∈ D := (hmemD t).mpr (Or.inr (by rw [ht]; exact C.one_mem))
  have hDnorm : ∀ d ∈ D, ∀ c ∈ C, d * c * d⁻¹ ∈ C := by
    intro d hd c hc
    rcases (hmemD d).mp hd with hdC | hdC
    · exact C.mul_mem (C.mul_mem hdC hc) (C.inv_mem hdC)
    · have e : d * c * d⁻¹ = t * ((t * d) * c * (t * d)⁻¹) * t := by
        calc d * c * d⁻¹ = (t * t) * (d * c * d⁻¹) * (t * t) := by rw [ht, one_mul, mul_one]
          _ = t * ((t * d) * c * (t * d)⁻¹) * t := by rw [mul_inv_rev, htinv]; group
      rw [e]
      exact htc _ (C.mul_mem (C.mul_mem hdC hc) (C.inv_mem hdC))
  have htord : orderOf t = 2 :=
    orderOf_eq_prime (by rw [sq, ht]) (fun h => htC (h ▸ C.one_mem))
  have hpt : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htord, pow_one])
  have htRn : Subgroup.zpowers t ≤ Subgroup.normalizer (R : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro r hr
    exact (htR r hr).symm
  have hR' : IsPGroup 2 (Subgroup.zpowers t ⊔ R : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hpt hR htRn
  have hR'D : Subgroup.zpowers t ⊔ R ≤ D := sup_le (Subgroup.zpowers_le.mpr htD) (hRC.trans hCD)
  have hjD : t * k ∈ D := (hmemD _).mpr (Or.inr (by rw [← mul_assoc, ht, one_mul]; exact hk))
  have hpj : IsPGroup 2 (Subgroup.zpowers (t * k)) := by
    have hdvd : orderOf (t * k) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hj)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
  have hR'G : IsPGroup 2 ((Subgroup.zpowers t ⊔ R).subgroupOf D) :=
    hR'.of_equiv (Subgroup.subgroupOfEquivOfLe hR'D).symm
  have hjG : IsPGroup 2 ((Subgroup.zpowers (t * k)).subgroupOf D) :=
    hpj.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hjD)).symm
  obtain ⟨Q, hQ⟩ := hR'G.exists_le_sylow
  obtain ⟨Qj, hQj⟩ := hjG.exists_le_sylow
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D Q Qj
  set QG := (Q : Subgroup D).map D.subtype with hQGdef
  have hQGp : IsPGroup 2 QG := Q.isPGroup'.map _
  have hRQG : R ≤ QG := fun r hr =>
    ⟨⟨r, hCD (hRC hr)⟩, hQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hr)), rfl⟩
  have htQG : t ∈ QG :=
    ⟨⟨t, htD⟩, hQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))),
      rfl⟩
  have hQGC : QG ⊓ C = R := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (le_inf hRQG hRC)
    exact hRmax _ inf_le_right (hQGp.to_le inf_le_left)
  have hQGsplit : ∀ q ∈ QG, q ∉ C → t * q ∈ R := by
    intro q hq hqC
    have htq : t * q ∈ C := ((hmemD q).mp (Subgroup.map_subtype_le _ hq)).resolve_left hqC
    have h : t * q ∈ QG ⊓ C := ⟨QG.mul_mem htQG hq, htq⟩
    rwa [hQGC] at h
  have hjQj : (⟨t * k, hjD⟩ : D) ∈ (Qj : Subgroup D) :=
    hQj (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _))
  rw [← hd, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hjQj
  have hj'Q : d⁻¹ * ⟨t * k, hjD⟩ * d ∈ (Q : Subgroup D) := by simpa using hjQj
  have hj' : (d : G)⁻¹ * (t * k) * d ∈ QG := ⟨_, hj'Q, rfl⟩
  have hj'C : (d : G)⁻¹ * (t * k) * d ∉ C := by
    intro h
    have h1 := hDnorm d d.2 _ h
    have h2 : t * k ∈ C := by simpa [mul_assoc] using h1
    exact htC (by simpa using C.mul_mem h2 (C.inv_mem hk))
  obtain ⟨r, hr, hj'eq⟩ : ∃ r ∈ R, (d : G)⁻¹ * (t * k) * d = t * r :=
    ⟨_, hQGsplit _ hj' hj'C, by rw [← mul_assoc t t, ht, one_mul]⟩
  have hj'2 : (t * r) * (t * r) = 1 := by
    rw [← hj'eq]
    calc (d : G)⁻¹ * (t * k) * d * ((d : G)⁻¹ * (t * k) * d) =
        (d : G)⁻¹ * ((t * k) * (t * k)) * d := by group
      _ = 1 := by rw [hj]; group
  have hr2 : r * r = 1 := by
    calc r * r = r * (t * t) * r := by rw [ht, mul_one]
      _ = (r * t) * (t * r) := by group
      _ = (t * r) * (t * r) := by rw [← htR r hr]
      _ = 1 := hj'2
  have hcases : (d : G)⁻¹ * (t * k) * d = t ∨ (d : G)⁻¹ * (t * k) * d = t * z := by
    rcases hinv r hr hr2 with h1 | hz
    · left
      rw [hj'eq, h1, mul_one]
    · right
      rw [hj'eq, hz]
  rcases (hmemD d).mp d.2 with hdC | hdC
  · exact ⟨(d : G)⁻¹, C.inv_mem hdC, by simpa using hcases⟩
  · refine ⟨(t * d)⁻¹ * k, C.mul_mem (C.inv_mem hdC) hk, ?_⟩
    have e : ((t * d)⁻¹ * k) * (t * k) * ((t * d)⁻¹ * k)⁻¹ = (d : G)⁻¹ * (t * k) * d := by
      calc ((t * d)⁻¹ * k) * (t * k) * ((t * d)⁻¹ * k)⁻¹ =
          (d : G)⁻¹ * t⁻¹ * k * (t * t) * d := by group
        _ = (d : G)⁻¹ * (t * k) * d := by rw [ht, mul_one, htinv]; group
    rw [e]
    exact hcases

theorem exists_normal_four_quotient_oddCore {W : Type*} [Group W] [Finite W]
    {C₀ : Subgroup W} (hC₀ : C₀.Normal) (hindex : C₀.index ≤ 2)
    {x : W} (hxc : x ∈ Subgroup.center W) (hx : orderOf x = 2)
    {E T : Subgroup W} (hE : Odd (Nat.card E)) (hEC₀ : E ≤ C₀)
    (hEn : ∀ c ∈ C₀, ∀ e ∈ E, c * e * c⁻¹ ∈ E)
    (hT : IsPGroup 2 T) (hTC₀ : T ≤ C₀) (hTcyc : IsCyclic T)
    {u : W} (huT : u ∈ T) (hu : orderOf u = 4) (hux : u ^ 2 = x)
    (hconj : ∀ c ∈ C₀, ∃ e ∈ E, ∃ τ ∈ T, c * u * c⁻¹ = e * τ) :
    ∃ B : Subgroup (W ⧸ CFSG.Assembly.oddCore W), B.Normal ∧
      (Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
        Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Assembly.oddCore W with hOdef
  have hO : O = CFSG.OrderReductions.OddCore.oddCore W := assembly_oddCore_eq W
  have hOodd : Odd (Nat.card O) := hO ▸ CFSG.OrderReductions.OddCore.oddCore_odd W
  have hEO : E ≤ O := by
    have := hC₀
    have hEn' : (E.subgroupOf C₀).Normal := ⟨fun a ha c => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      simpa using hEn c c.2 a ha⟩
    have hodd' : Odd (Nat.card (E.subgroupOf C₀)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC₀).toEquiv]
    have h1 := CFSG.OrderReductions.OddCore.normal_le_oddCore (E.subgroupOf C₀) hodd'
    have h2 := CFSG.OrderReductions.OddCore.normal_subgroup_oddCore_map_le C₀
    intro e he
    rw [hO]
    exact h2 ⟨⟨e, hEC₀ he⟩, h1 (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  set q := QuotientGroup.mk' O with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective O
  have hqker : ∀ w, q w = 1 ↔ w ∈ O := fun w => QuotientGroup.eq_one_iff w
  have hTO : ∀ τ ∈ T, τ ∈ O → τ = 1 := by
    intro τ hτT hτO
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨τ, hτT⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd := Subgroup.orderOf_dvd_natCard O hτO
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hOodd)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hxT : x ∈ T := hux ▸ Subgroup.pow_mem _ huT 2
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have hqx : q x ≠ 1 := fun h => hx1 (hTO x hxT ((hqker x).mp h))
  have hqx2 : q x ^ 2 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hqxord : orderOf (q x) = 2 := orderOf_eq_prime hqx2 hqx
  have hqxc : q x ∈ Subgroup.center (W ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro w'
    obtain ⟨w, rfl⟩ := hq w'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hxc w]
  have hqu4 : orderOf (q u) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := q u)
      (by rw [pow_one, ← map_pow, hux]; exact hqx)
      (by rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow, ← hu, pow_orderOf_eq_one, map_one])
    rw [h]
    norm_num
  have hBcard : Nat.card (Subgroup.zpowers (q u)) = 4 := by rw [Nat.card_zpowers, hqu4]
  have hzB : q x ∈ Subgroup.zpowers (q u) := by
    rw [← hux, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  have hC₀q : (C₀.map q).Normal := hC₀.map q hq
  have hindexq : (C₀.map q).index ≤ 2 := by
    have hdvd := Subgroup.index_map_dvd (H := C₀) hq
    have hpos : 0 < C₀.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd hpos hdvd).trans hindex
  have hBC₀q : Subgroup.zpowers (q u) ≤ C₀.map q :=
    Subgroup.zpowers_le.mpr ⟨u, hTC₀ huT, rfl⟩
  have hBn : ((Subgroup.zpowers (q u)).subgroupOf (C₀.map q)).Normal := by
    constructor
    intro b hb c
    rw [Subgroup.mem_subgroupOf] at hb ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨c', hc'C₀, hc'⟩ := Subgroup.mem_map.mp c.2
    obtain ⟨e, he, τ, hτ, hcu⟩ := hconj c' hc'C₀
    have h2 : q (c' * u * c'⁻¹) = q τ := by
      rw [hcu, map_mul, (hqker e).mpr (hEO he), one_mul]
    have hτ4 : τ ^ 4 = 1 := by
      have h1 : (c' * u * c'⁻¹) ^ 4 = 1 := by
        rw [conj_pow, ← hu, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      have h3 : q (τ ^ 4) = 1 := by rw [map_pow, ← h2, ← map_pow, h1, map_one]
      exact hTO _ (Subgroup.pow_mem _ hτ 4) ((hqker _).mp h3)
    have hτu : τ ∈ Subgroup.zpowers u :=
      mem_zpowers_of_orderOf_dvd_of_isCyclic hTcyc hτ huT
        (by rw [hu]; exact orderOf_dvd_of_pow_eq_one hτ4)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hτu
    refine Subgroup.mem_zpowers_iff.mpr ⟨j * k, ?_⟩
    calc q u ^ (j * k) = (q (u ^ j)) ^ k := by rw [map_zpow, zpow_mul]
      _ = (q τ) ^ k := by rw [hj]
      _ = (q (c' * u * c'⁻¹)) ^ k := by rw [h2]
      _ = (c : W ⧸ O) * b * (c : W ⧸ O)⁻¹ := by
        rw [← hk, map_mul, map_mul, map_inv, hc', conj_zpow]
  exact index_two_normal_cyclic_four_central_involution_obstruction
    hC₀q hindexq hqxc hqxord hBC₀q hBn (Subgroup.isCyclic_zpowers _) hBcard hzB

end CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

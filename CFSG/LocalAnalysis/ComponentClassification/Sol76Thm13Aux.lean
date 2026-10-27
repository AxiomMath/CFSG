module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm33

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Open

variable {G : Type} [Group G]

theorem aschbacherThm5OddCore_eq_pPrimeCore' (X : Type*) [Group X] :
    aschbacherThm5OddCore X = pPrimeCore 2 X := by
  unfold aschbacherThm5OddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem aschbacherThm5Core_eq_oddCoreIn (D : Subgroup G) : aschbacherThm5Core D = oddCoreIn D := by
  rw [aschbacherThm5Core, aschbacherThm5OddCore_eq_pPrimeCore', oddCoreIn]

theorem aschbacherThm5Preimage_map_subgroupOf {D K : Subgroup G} (hKD : K ≤ D) :
    aschbacherThm5Preimage D
        ((K.subgroupOf D).map (QuotientGroup.mk' (aschbacherThm5OddCore D))) =
      K ⊔ oddCoreIn D := by
  rw [aschbacherThm5Preimage, Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hKD, aschbacherThm5OddCore_eq_pPrimeCore', oddCoreIn]

theorem isSubnormal_subgroupOf_of_le {K D N : Subgroup G} (hDN : D ≤ N)
    (h : (K.subgroupOf N).IsSubnormal) : (K.subgroupOf D).IsSubnormal := by
  have h1 := h.subgroupOf (K := D.subgroupOf N)
  have h2 := h1.map (f := (subgroupOfEquivOfLe hDN).toMonoidHom)
    (subgroupOfEquivOfLe hDN).surjective
  convert h2 using 1
  ext x
  constructor
  · intro hx
    refine ⟨⟨⟨x, hDN x.2⟩, x.2⟩, ?_, rfl⟩
    simpa [mem_subgroupOf] using hx
  · rintro ⟨y, hy, rfl⟩
    simpa [mem_subgroupOf] using hy

theorem le_normalizer_map_subtype' {N : Subgroup G} (H : Subgroup N) [H.Normal] :
    N ≤ normalizer ((H.map N.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := H) N.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

variable [Finite G]

theorem isTwoComponentIn_of_le {K D N : Subgroup G} (hK : IsTwoComponentIn K N) (hKD : K ≤ D)
    (hDN : D ≤ N) : IsTwoComponentIn K D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKN, hKp⟩ := hK
  rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K N hKN] at hKp
  refine ⟨hKD, ?_⟩
  rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K D hKD]
  exact ⟨isSubnormal_subgroupOf_of_le hDN hKp.1, hKp.2⟩

omit [Finite G] in
theorem inf_le_oddCoreIn {A K : Subgroup G} (hA : Nat.Coprime 2 (Nat.card A))
    (hKA : K ≤ normalizer (A : Set G)) : A ⊓ K ≤ oddCoreIn K := by
  rintro x ⟨hxA, hxK⟩
  have hn : (A.subgroupOf K).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer_inf]
    intro k hk
    rw [mem_normalizer_iff]
    intro y
    have h1 := mem_normalizer_iff.mp (hKA hk) y
    have h2 := mem_normalizer_iff.mp (le_normalizer hk) y
    rw [mem_inf, mem_inf, h1, h2]
  have hodd : Nat.Coprime 2 (Nat.card ↥(A.subgroupOf K)) := by
    have h1 : Nat.card ↥(A.subgroupOf K) ∣ Nat.card ↥A := by
      rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.coprime_dvd_right h1 hA
  have hle : A.subgroupOf K ≤ pPrimeCore 2 ↥K := le_sSup ⟨hn, hodd⟩
  exact ⟨⟨x, hxK⟩, hle (show (⟨x, hxK⟩ : K) ∈ A.subgroupOf K from hxA), rfl⟩

theorem coprime_card_oddCoreIn (N : Subgroup G) : Nat.Coprime 2 (Nat.card ↥(oddCoreIn N)) := by
  rw [oddCoreIn, Subgroup.card_map_of_injective N.subtype_injective]
  exact pPrimeCore_coprime_card

theorem oddCoreIn_inf_le {D N : Subgroup G} (hDN : D ≤ N) : oddCoreIn N ⊓ D ≤ oddCoreIn D :=
  inf_le_oddCoreIn (coprime_card_oddCoreIn N)
    (hDN.trans (le_normalizer_map_subtype' (pPrimeCore 2 ↥N)))

theorem inf_oddCoreIn_eq {K D : Subgroup G} (hK : IsTwoComponentIn K D) :
    K ⊓ oddCoreIn D = oddCoreIn K := by
  refine le_antisymm ?_ (le_inf (map_subtype_le _) (oddCoreIn_le_of_isTwoComponentIn hK))
  rw [inf_comm]
  exact inf_le_oddCoreIn (coprime_card_oddCoreIn D)
    (hK.1.trans (le_normalizer_map_subtype' (pPrimeCore 2 ↥D)))

theorem isQuasisimple_image {K D : Subgroup G} (hK : IsTwoComponentIn K D) (O : Subgroup ↥D)
    [O.Normal] (hO : O = pPrimeCore 2 ↥D) :
    IsQuasisimple ↥((K.subgroupOf D).map (QuotientGroup.mk' O)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥K →* ↥D ⧸ O := (QuotientGroup.mk' O).comp (inclusion hK.1) with hφ
  have hrange : φ.range = (K.subgroupOf D).map (QuotientGroup.mk' O) := by
    rw [hφ, MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ.ker = pPrimeCore 2 ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hO]
    have h1 := inf_oddCoreIn_eq hK
    constructor
    · intro hx
      have hxO : (x : G) ∈ K ⊓ oddCoreIn D := ⟨x.2, ⟨inclusion hK.1 x, hx, rfl⟩⟩
      rw [h1] at hxO
      obtain ⟨y, hy, hyx⟩ := hxO
      rwa [Subtype.ext hyx] at hy
    · intro hx
      have hxO : (x : G) ∈ oddCoreIn K := ⟨x, hx, rfl⟩
      rw [← h1] at hxO
      obtain ⟨y, hy, hyx⟩ := hxO.2
      have : y = inclusion hK.1 x := Subtype.ext hyx
      rwa [this] at hy
  have hq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K D hK.1).mp hK.2).2.2
  let e : ↥K ⧸ pPrimeCore 2 ↥K ≃* ↥((K.subgroupOf D).map (QuotientGroup.mk' O)) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)
  exact LocalCores.isQuasisimple_of_mulEquiv e hq

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {D : Subgroup G} {h : G} (hh : h ∈ normalizer (D : Set G)) :
    D.map (MulAut.conj h).toMonoidHom = D := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hh y).mp hy
  · intro hx
    refine ⟨h⁻¹ * x * h, (mem_normalizer_iff.mp hh _).mpr ?_, ?_⟩
    · simpa [mul_assoc] using hx
    · simp [mul_assoc]

omit [Finite G] in
@[expose] noncomputable def conjAutOf {D : Subgroup G} {h : G} (hh : h ∈ normalizer (D : Set G)) :
    ↥D ≃* ↥D :=
  (D.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective).trans
    (MulEquiv.subgroupCongr (map_conj_eq_of_mem_normalizer hh))

omit [Finite G] in
theorem conjAutOf_apply {D : Subgroup G} {h : G} (hh : h ∈ normalizer (D : Set G)) (x : D) :
    ((conjAutOf hh x : D) : G) = h * x * h⁻¹ := rfl

omit [Finite G] in
theorem map_conj_oddCoreIn {D : Subgroup G} {h : G} (hh : h ∈ normalizer (D : Set G)) :
    (oddCoreIn D).map (MulAut.conj h).toMonoidHom = oddCoreIn D := by
  have h1 := pPrimeCore_map_iso 2 (conjAutOf hh)
  rw [oddCoreIn, Subgroup.map_map]
  conv_rhs => rw [← h1, Subgroup.map_map]
  congr 1

omit [Finite G] in
theorem isTwoComponentIn_map_conj {K D : Subgroup G} (hK : IsTwoComponentIn K D) {h : G}
    (hh : h ∈ normalizer (D : Set G)) :
    IsTwoComponentIn (K.map (MulAut.conj h).toMonoidHom) D := by
  have hmap : (K.subgroupOf D).map (conjAutOf hh).toMonoidHom =
      (K.map (MulAut.conj h).toMonoidHom).subgroupOf D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨k, hk, hkx⟩
      refine ⟨⟨k, hK.1 hk⟩, hk, Subtype.ext ?_⟩
      rw [MulEquiv.coe_toMonoidHom, conjAutOf_apply]
      simpa using hkx
  refine ⟨?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_conj_eq_of_mem_normalizer hh]
    exact ⟨k, hK.1 hk, rfl⟩
  · rw [← hmap]
    exact LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (conjAutOf hh) hK.2

omit [Finite G] in
theorem iSup_map_subgroupOf_eq_top {D : Subgroup G} {r : ℕ} {K : Fin r → Subgroup G}
    (hKD : ∀ i, K i ≤ D) (hgen : ⨆ i, K i = D) (O : Subgroup ↥D) [O.Normal] :
    ⨆ j, ((K j).subgroupOf D).map (QuotientGroup.mk' O) = ⊤ := by
  rw [← Subgroup.map_iSup, ← map_top_of_surjective _ (QuotientGroup.mk'_surjective O)]
  congr 1
  apply Subgroup.map_injective D.subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simp only [Subgroup.map_subgroupOf_eq_of_le (hKD _)]
  exact hgen

theorem exists_map_conj_eq {D : Subgroup G} {r : ℕ} {K : Fin r → Subgroup G}
    (hK : ∀ i, IsTwoComponentIn (K i) D) (hgen : ⨆ i, K i = D) {h : G}
    (hh : h ∈ normalizer (D : Set G)) (i : Fin r) :
    ∃ j, (K i ⊔ oddCoreIn D).map (MulAut.conj h).toMonoidHom = K j ⊔ oddCoreIn D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥D) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcomp : ∀ X : Subgroup G, IsTwoComponentIn X D → IsComponent ((X.subgroupOf D).map π) := by
    intro X hX
    refine ⟨isQuasisimple_image hX _ rfl, ?_⟩
    exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 X D hX.1).mp hX.2).1.map hsurj
  have hYt := isTwoComponentIn_map_conj (hK i) hh
  set Y := (K i).map (MulAut.conj h).toMonoidHom with hY
  have hYc := hcomp Y hYt
  have hgen' := iSup_map_subgroupOf_eq_top (fun j => (hK j).1) hgen (pPrimeCore 2 ↥D)
  obtain ⟨j, hj⟩ : ∃ j, (Y.subgroupOf D).map π = ((K j).subgroupOf D).map π := by
    by_contra hne
    push Not at hne
    have hc : ∀ j, ⁅(Y.subgroupOf D).map π, ((K j).subgroupOf D).map π⁆ = ⊥ := fun j =>
      (LocalCores.distinct_components_commute hYc (hcomp _ (hK j))).resolve_left (hne j)
    have hcen : ⊤ ≤ centralizer ((Y.subgroupOf D).map π : Set (↥D ⧸ pPrimeCore 2 ↥D)) := by
      rw [← hgen']
      refine iSup_le fun j => ?_
      have h1 := hc j
      rw [commutator_comm] at h1
      exact commutator_eq_bot_iff_le_centralizer.mp h1
    obtain ⟨-, -, a, b, hab⟩ := hYc.1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp (hcen (mem_top (b : _))) a a.2)
  refine ⟨j, ?_⟩
  have hpre : ∀ X : Subgroup G, X ≤ D →
      (((X.subgroupOf D).map π).comap π).map D.subtype = X ⊔ oddCoreIn D := by
    intro X hXD
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hXD, oddCoreIn]
  rw [Subgroup.map_sup, map_conj_oddCoreIn hh, ← hY, ← hpre Y hYt.1, hj, hpre (K j) (hK j).1]

omit [Finite G] in
theorem exists_conj_of_involution {O : Subgroup G} (hO : Odd (Nat.card O)) {b x : G}
    (hb : b * b = 1) (hx : x * x = 1) (hxO : x * b ∈ O) :
    ∃ c ∈ O, x = c * b * c⁻¹ := by
  set o := x * b with hodef
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hxo : x = o * b := by rw [hodef, mul_assoc, hb, mul_one]
  have hinv : b * o * b⁻¹ = o⁻¹ := by
    rw [hbinv]
    have h1 : o * b * (o * b) = 1 := by rw [← hxo]; exact hx
    calc b * o * b = o⁻¹ * (o * b * (o * b)) := by group
      _ = o⁻¹ := by rw [h1, mul_one]
  have hoodd : Odd (orderOf o) := by
    have h1 := orderOf_dvd_natCard (⟨o, hxO⟩ : O)
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hO h1
  obtain ⟨k, hk⟩ := hoodd
  set u := o ^ (k + 1) with hu
  have hu2 : u * u = o := by
    rw [hu, ← pow_add, show k + 1 + (k + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hbu : b * u * b⁻¹ = u⁻¹ := by
    rw [hu, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinv, inv_pow]
  refine ⟨u, O.pow_mem hxO _, ?_⟩
  calc x = o * b := hxo
    _ = u * u * b := by rw [hu2]
    _ = u * (b * u * b⁻¹)⁻¹ * b := by rw [hbu, inv_inv]
    _ = u * b * u⁻¹ := by group

theorem exists_conj_commute {O : Subgroup G} (hO : Odd (Nat.card O)) {b t : G}
    (hb : b * b = 1) (hbO : b ∈ normalizer (O : Set G)) (htO : t ∈ normalizer (O : Set G))
    (htb : t * b * t⁻¹ * b ∈ O) {k : ℕ} (ht : t ^ (2 ^ k) = 1) :
    ∃ c ∈ O, t * (c * b * c⁻¹) = c * b * c⁻¹ * t := by
  classical
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  set O' : Subgroup (ConjAct G) := O.map (MulEquiv.toMonoidHom ConjAct.toConjAct) with hO'
  set X := MulAction.orbit O' b with hX
  have : Fintype X := Fintype.ofFinite X
  have hmemX : ∀ x : G, x ∈ X ↔ ∃ c ∈ O, x = c * b * c⁻¹ := by
    intro x
    rw [hX, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨⟨c, ⟨c₀, hc₀, rfl⟩⟩, rfl⟩
      exact ⟨c₀, hc₀, by rw [Subgroup.smul_def, ConjAct.smul_def]; rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨ConjAct.toConjAct c, ⟨c, hc, rfl⟩⟩, by rw [Subgroup.smul_def, ConjAct.smul_def]; rfl⟩
  have hstab : ∀ s : G, s ∈ normalizer (O : Set G) → s * b * s⁻¹ * b ∈ O →
      ∀ x ∈ X, s * x * s⁻¹ ∈ X := by
    intro s hsO hsb x hx
    obtain ⟨c, hc, rfl⟩ := (hmemX x).mp hx
    rw [hmemX]
    apply exists_conj_of_involution hO hb
    · have h1 : c * b * c⁻¹ * (c * b * c⁻¹) = 1 := by
        calc c * b * c⁻¹ * (c * b * c⁻¹) = c * (b * b) * c⁻¹ := by group
          _ = 1 := by rw [hb]; group
      calc s * (c * b * c⁻¹) * s⁻¹ * (s * (c * b * c⁻¹) * s⁻¹)
          = s * (c * b * c⁻¹ * (c * b * c⁻¹)) * s⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · set d := s * c * s⁻¹ with hd
      have hdO : d ∈ O := (mem_normalizer_iff.mp hsO c).mp hc
      have hdO' : b * d⁻¹ * b⁻¹ ∈ O := (mem_normalizer_iff.mp hbO _).mp (inv_mem hdO)
      have h1 : s * (c * b * c⁻¹) * s⁻¹ * b = d * (s * b * s⁻¹ * b) * (b * d⁻¹ * b⁻¹) := by
        rw [show d * (s * b * s⁻¹ * b) * (b * d⁻¹ * b⁻¹) =
            d * s * b * s⁻¹ * (b * b) * d⁻¹ * b⁻¹ by group, hb, hd, hbinv]
        group
      rw [h1]
      exact mul_mem (mul_mem hdO hsb) hdO'
  have htinvb : t⁻¹ * b * t⁻¹⁻¹ * b ∈ O := by
    have h1 := (mem_normalizer_iff''.mp htO _).mp htb
    have h2 : t⁻¹ * b * t⁻¹⁻¹ * b = (t⁻¹ * (t * b * t⁻¹ * b) * t)⁻¹ := by
      rw [show (t⁻¹ * (t * b * t⁻¹ * b) * t)⁻¹ = t⁻¹ * b⁻¹ * t * b⁻¹ by group, hbinv]
      group
    rw [h2]
    exact inv_mem h1
  have hXt := hstab t htO htb
  have hXt' := hstab t⁻¹ (inv_mem htO) htinvb
  let σ : Equiv.Perm X :=
    { toFun := fun x => ⟨t * x * t⁻¹, hXt x x.2⟩
      invFun := fun x => ⟨t⁻¹ * x * t⁻¹⁻¹, hXt' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  have hσpow : ∀ n : ℕ, ∀ x : X, ((σ ^ n) x : G) = t ^ n * x * (t ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      show t * (((σ ^ n) x : X) : G) * t⁻¹ = t ^ (n + 1) * x * (t ^ (n + 1))⁻¹
      rw [ih, pow_succ']
      group
  have hσ : σ ^ 2 ^ k = 1 := by
    ext x
    rw [hσpow, ht]
    simp
  have hXodd : ¬ 2 ∣ Fintype.card X := by
    have h1 := MulAction.index_stabilizer O' b
    have h2 : (MulAction.stabilizer O' b).index ∣ Nat.card O' := Subgroup.index_dvd_card _
    have h3 : Nat.card O' = Nat.card O :=
      Subgroup.card_map_of_injective (ConjAct.toConjAct (G := G)).injective
    rw [h1, h3, Set.ncard_eq_toFinset_card', Set.toFinset_card] at h2
    intro h4
    obtain ⟨m, hm⟩ := hO
    have h5 := h4.trans h2
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hXodd hσ
  obtain ⟨c, hc, hcx⟩ := (hmemX x).mp x.2
  refine ⟨c, hc, ?_⟩
  have h1 : t * x * t⁻¹ = x := congrArg Subtype.val hx
  rw [← hcx]
  calc t * (x : G) = t * x * t⁻¹ * t := by group
    _ = x * t := by rw [h1]

theorem mem_normalizer_of_conj_mem {O : Subgroup G} {t : G}
    (h : ∀ o ∈ O, t⁻¹ * o * t ∈ O) : t ∈ normalizer (O : Set G) := by
  have hle : O.map (MulAut.conj t⁻¹).toMonoidHom ≤ O := by
    rintro _ ⟨o, ho, rfl⟩
    simpa [MulAut.conj_apply] using h o ho
  have heq : O.map (MulAut.conj t⁻¹).toMonoidHom = O :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective])
  rw [mem_normalizer_iff'']
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨o, ho, hox⟩ := hx
  have : o = x := by
    simpa [MulAut.conj_apply] using hox
  rwa [← this]

theorem mem_of_centralizes_quotient {K D H : Subgroup G} (hKD : K ≤ D) (hDH : D ≤ H)
    {b : G} (hbK : b ∈ K) (hb : orderOf b = 2) (hCb : centralizer ({b} : Set G) ≤ H)
    {t : G} {k : ℕ} (ht : t ^ (2 ^ k) = 1)
    (htc : ∀ a ∈ K ⊔ oddCoreIn D, t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn D) : t ∈ H := by
  set O := oddCoreIn D with hOdef
  have hbb : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn D)
  have hDO : D ≤ normalizer (O : Set G) := le_normalizer_map_subtype' (pPrimeCore 2 ↥D)
  have htO : t ∈ normalizer (O : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro o ho
    have h1 := htc o⁻¹ (mem_sup_right (inv_mem ho))
    have h2 : t⁻¹ * o * t = t⁻¹ * o⁻¹⁻¹ * t * o⁻¹ * o := by group
    rw [h2]
    exact mul_mem h1 ho
  have htb : t * b * t⁻¹ * b ∈ O := by
    have h1 := htc b (mem_sup_left hbK)
    have h2 := (mem_normalizer_iff.mp htO _).mp h1
    have h3 : t * b * t⁻¹ * b = (t * (t⁻¹ * b⁻¹ * t * b) * t⁻¹)⁻¹ := by
      rw [show (t * (t⁻¹ * b⁻¹ * t * b) * t⁻¹)⁻¹ = t * b⁻¹ * t⁻¹ * b by group, hbinv]
    rw [h3]
    exact inv_mem h2
  obtain ⟨c, hc, hcomm⟩ := exists_conj_commute hOodd hbb (hDO (hKD hbK)) htO htb ht
  have hcH : c ∈ H := hDH (map_subtype_le _ hc)
  have h1 : c⁻¹ * t * c ∈ centralizer ({b} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc c⁻¹ * t * c * b = c⁻¹ * (t * (c * b * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * b * c⁻¹ * t) * c := by rw [hcomm]
      _ = b * (c⁻¹ * t * c) := by group
  have h2 := hCb h1
  have h3 : t = c * (c⁻¹ * t * c) * c⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hcH h2) (inv_mem hcH)

theorem le_solomonKStarOf_top {K D : Subgroup G} (hK : IsTwoComponentIn K D) (hD : D.Normal)
    (hKs : K ∈ solomonKStar G) : K ≤ solomonKStarOf (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsubD := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K D hK.1).mp hK.2
  have hsubG : K.IsSubnormal := Subgroup.IsSubnormal.trans hK.1 hsubD.1 hD.isSubnormal
  have htop : IsTwoComponentIn K ⊤ :=
    ⟨le_top, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K ⊤ le_top).mpr
      ⟨hsubG.subgroupOf, hsubD.2⟩⟩
  exact le_iSup₂_of_le K ⟨htop, hKs⟩ le_rfl

theorem two_le_pRank_of_mem_solomonKStar {K : Subgroup G} (hK : K ∈ solomonKStar G) :
    2 ≤ CFSG.Open.pRank 2 K := by
  have h1 := hK.2.2 K ⟨hK.2.1, Relation.ReflTransGen.refl⟩
  rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1

theorem exists_orderOf_eq_two_of_pRank {K : Subgroup G} (hK : 1 ≤ CFSG.Open.pRank 2 K) :
    ∃ b ∈ K, orderOf b = 2 := by
  obtain ⟨E, hEK, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) K
  have h2 : 1 < Nat.card E := by
    rw [hcard]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 K := Nat.pow_le_pow_right (by norm_num) hK
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp h2
  obtain ⟨e, he⟩ := exists_ne (1 : E)
  refine ⟨e, hEK e.2, ?_⟩
  have he' : (e : G) ≠ 1 := fun h => he (Subtype.ext h)
  exact orderOf_eq_prime (hE.2 e e.2) he'

end CFSG.ComponentClassification.Sol76

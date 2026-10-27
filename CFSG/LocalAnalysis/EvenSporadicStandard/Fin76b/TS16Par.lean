module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Loc

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type*} [Group G]

@[expose] def conjSet (M : Subgroup G) (z : G) : Set G := {y | ∃ m ∈ M, y = m * z * m⁻¹}

@[expose, reducible] def conjSetAction {M Q : Subgroup G} (hQM : Q ≤ M) (z : G) :
    MulAction Q (conjSet M z) where
  smul q y := ⟨(q : G) * y * (q : G)⁻¹, by
    obtain ⟨m, hm, hy⟩ := y.2
    exact ⟨q * m, M.mul_mem (hQM q.2) hm, by rw [hy]; group⟩⟩
  one_smul y := Subtype.ext (show ((1 : Q) : G) * y * ((1 : Q) : G)⁻¹ = y by simp)
  mul_smul p q y := Subtype.ext (show ((p * q : Q) : G) * y * ((p * q : Q) : G)⁻¹ =
    (p : G) * ((q : G) * y * (q : G)⁻¹) * (p : G)⁻¹ by simp only [Subgroup.coe_mul]; group)

theorem conjSetAction_smul_coe {M Q : Subgroup G} (hQM : Q ≤ M) {z : G} (q : Q)
    (y : conjSet M z) :
    letI := conjSetAction hQM z
    ((q • y : conjSet M z) : G) = (q : G) * y * (q : G)⁻¹ := rfl

theorem card_stabilizer_conjSetAction {M Q : Subgroup G} (hQM : Q ≤ M) {z : G}
    (y : conjSet M z) :
    letI := conjSetAction hQM z
    Nat.card (MulAction.stabilizer Q y) = Nat.card ↥(Q ⊓ centralizer ({(y : G)} : Set G)) := by
  let := conjSetAction hQM z
  have h : MulAction.stabilizer Q y = (Q ⊓ centralizer ({(y : G)} : Set G)).subgroupOf Q := by
    ext q
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, conjSetAction_smul_coe]
    constructor
    · intro hq
      refine ⟨q.2, ?_⟩
      calc (q : G) * y = q * y * (q : G)⁻¹ * q := by group
        _ = y * q := by rw [hq]
    · rintro ⟨-, hq⟩
      calc (q : G) * y * (q : G)⁻¹ = y * q * (q : G)⁻¹ := by rw [hq]
        _ = y := by group
  rw [h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_le_of_mem_conjSet [Finite G] {M : Subgroup G} {z y : G} {c : ℕ}
    (hy : y ∈ conjSet M z)
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ M ⊓ centralizer ({z} : Set G) → Nat.card R ≤ c)
    (T : Subgroup G) (hT : IsPGroup 2 T) (hTle : T ≤ M ⊓ centralizer ({y} : Set G)) :
    Nat.card T ≤ c := by
  obtain ⟨m, hm, rfl⟩ := hy
  let f := (MulAut.conj m⁻¹).toMonoidHom
  have hinj : Function.Injective f := (MulAut.conj m⁻¹).injective
  rw [← Subgroup.card_map_of_injective hinj]
  refine hmax _ (hT.map f) ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨htM, htC⟩ := Subgroup.mem_inf.1 (hTle ht)
  rw [Subgroup.mem_centralizer_singleton_iff] at htC
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show m⁻¹ * t * m⁻¹⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem (M.inv_mem hm) htM) (M.inv_mem (M.inv_mem hm))
  · rw [Subgroup.mem_centralizer_singleton_iff]
    show m⁻¹ * t * m⁻¹⁻¹ * z = z * (m⁻¹ * t * m⁻¹⁻¹)
    have h1 : t * (m * z * m⁻¹) * t⁻¹ = m * z * m⁻¹ := by rw [htC]; group
    calc m⁻¹ * t * m⁻¹⁻¹ * z = m⁻¹ * (t * (m * z * m⁻¹) * t⁻¹) * t * m := by group
      _ = z * (m⁻¹ * t * m⁻¹⁻¹) := by rw [h1]; group

theorem mem_of_card_eq [Finite G] {M Q : Subgroup G} {z y : G} {c : ℕ} (hQM : Q ≤ M)
    (hQ : IsPGroup 2 Q) (hzM : z ∈ M) (hz2 : z * z = 1) (hy : y ∈ conjSet M z)
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ M ⊓ centralizer ({z} : Set G) → Nat.card R ≤ c)
    (hc : Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) = c) : y ∈ Q := by
  have hyM : y ∈ M := by
    obtain ⟨m, hm, rfl⟩ := hy
    exact M.mul_mem (M.mul_mem hm hzM) (M.inv_mem hm)
  have hy2 : y * y = 1 := by
    obtain ⟨m, hm, rfl⟩ := hy
    calc m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  set S := Q ⊓ centralizer ({y} : Set G) with hS
  have hSp : IsPGroup 2 S := hQ.to_le inf_le_left
  have hYp : IsPGroup 2 (zpowers y) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    show (y ^ k) ^ (2 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hy2,
      one_zpow]
  have hnorm : S ≤ normalizer (zpowers y : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro s hs
    have hsy : s * y = y * s :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨k, rfl⟩
    exact ((Commute.zpow_left (show Commute y s from hsy.symm) k)).eq
  have hJp : IsPGroup 2 ↥(S ⊔ zpowers y) := IsPGroup.to_sup_of_normal_right' hSp hYp hnorm
  have hJle : S ⊔ zpowers y ≤ M ⊓ centralizer ({y} : Set G) := by
    refine sup_le (le_inf (inf_le_left.trans hQM) inf_le_right) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨hyM, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hcard := card_le_of_mem_conjSet hy hmax _ hJp hJle
  have heq : S = S ⊔ zpowers y := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc]; exact hcard)
  have hyS : y ∈ S := by
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  exact (Subgroup.mem_inf.1 hyS).1

theorem extremalParity : ExtremalParity := by
  intro G _ _ M Q z c hQM hQ hidx hzQ hz2 hex hmax
  classical
  obtain ⟨R, hR, hRle, hRc⟩ := hex
  have hzM : z ∈ M := hQM hzQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hQ
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hR
  rw [hb] at hRc
  subst hRc
  set K := M ⊓ centralizer ({z} : Set G) with hK
  set u := (Q.subgroupOf M).index with hu
  have hMu : Nat.card M = 2 ^ a * u := by
    rw [← ha, ← Subgroup.card_mul_index (Q.subgroupOf M)]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  have hu_odd : Odd u := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hidx)
  obtain ⟨v, hKv, hv_odd⟩ : ∃ v, Nat.card K = 2 ^ b * v ∧ Odd v := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
    have hP := P.card_eq_multiplicity
    have hle1 : Nat.card P ≤ 2 ^ b := by
      have h := hmax ((P : Subgroup K).map K.subtype) (P.isPGroup'.map _) (by
        rintro _ ⟨x, -, rfl⟩
        exact x.2)
      rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
    have hle2 : 2 ^ b ≤ Nat.card P := by
      have hRK : R ≤ K := hRle
      obtain ⟨P', hP'⟩ :=
        (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm).exists_le_sylow
      calc 2 ^ b = Nat.card (R.subgroupOf K) := by
            rw [← hb]
            exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv).symm
        _ ≤ Nat.card P' := Subgroup.card_le_of_le hP'
        _ = Nat.card P := by rw [P'.card_eq_multiplicity, P.card_eq_multiplicity]
    have hPb : Nat.card P = 2 ^ b := le_antisymm hle1 hle2
    refine ⟨ordCompl[2] (Nat.card K), ?_, ?_⟩
    · rw [← hPb, hP, Nat.ordProj_mul_ordCompl_eq_self]
    · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1
        (Nat.not_dvd_ordCompl Nat.prime_two Nat.card_pos.ne'))
  have hba : b ≤ a := by
    have h1 : 2 ^ b ∣ 2 ^ a * u := by
      rw [← hMu]
      exact (Dvd.intro v hKv.symm).trans (Subgroup.card_dvd_of_le inf_le_left)
    have h2 := (Nat.Coprime.pow_left b (Nat.coprime_two_left.2 hu_odd)).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
  have hX : Nat.card (conjSet M z) * Nat.card K = Nat.card M := by
    let := conjSetAction (le_refl M) z
    let z0 : conjSet M z := ⟨z, 1, M.one_mem, by group⟩
    have : MulAction.IsPretransitive M (conjSet M z) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨m₁, hm₁, hx⟩ := x.2
      obtain ⟨m₂, hm₂, hy⟩ := y.2
      refine ⟨⟨m₂ * m₁⁻¹, M.mul_mem hm₂ (M.inv_mem hm₁)⟩, Subtype.ext ?_⟩
      rw [conjSetAction_smul_coe, hx, hy]
      group
    rw [← MulAction.index_stabilizer_of_transitive M z0, hK,
      ← card_stabilizer_conjSetAction (le_refl M) z0]
    exact Subgroup.index_mul_card _
  let := conjSetAction hQM z
  have hstab : ∀ x : conjSet M z, ∃ e ≤ b,
      Nat.card ↥(Q ⊓ centralizer ({(x : G)} : Set G)) = 2 ^ e := by
    intro x
    obtain ⟨e, he⟩ := IsPGroup.iff_card.1
      (hQ.to_le (inf_le_left : Q ⊓ centralizer ({(x : G)} : Set G) ≤ Q))
    refine ⟨e, ?_, he⟩
    have h := card_le_of_mem_conjSet x.2 hmax _ (hQ.to_le inf_le_left)
      (le_inf (inf_le_left.trans hQM) inf_le_right)
    rw [he] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  choose e he_le he using hstab
  have hindex : ∀ x : conjSet M z,
      (MulAction.stabilizer Q x).index = 2 ^ (a - b) * 2 ^ (b - e x) := by
    intro x
    have h1 := Subgroup.index_mul_card (MulAction.stabilizer Q x)
    rw [card_stabilizer_conjSetAction hQM x, he x, ha] at h1
    rw [← pow_add]
    have h2 : 2 ^ (a - b + (b - e x)) * 2 ^ e x = 2 ^ a := by
      rw [← pow_add]
      congr 1
      have := he_le x
      omega
    exact Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans h2.symm)
  let Ω := Quotient (MulAction.orbitRel Q (conjSet M z))
  have : Fintype Ω := Fintype.ofFinite _
  have hsum : Nat.card (conjSet M z) = ∑ ω : Ω, (MulAction.stabilizer Q ω.out).index := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer Q (conjSet M z)),
      Nat.card_sigma]
    rfl
  set S := ∑ ω : Ω, 2 ^ (b - e ω.out) with hS
  have hXS : Nat.card (conjSet M z) = 2 ^ (a - b) * S := by
    rw [hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ω _ => hindex ω.out)
  have hSv : S * v = u := by
    have h := hX
    rw [hXS, hKv, hMu] at h
    have h2 : 2 ^ (a - b) * 2 ^ b = 2 ^ a := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : 2 ^ a * (S * v) = 2 ^ a * u := by
      rw [← h, ← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h3
  have hS_odd : Odd S := (Nat.odd_mul.1 (hSv ▸ hu_odd)).1
  have hcardodd : Odd (Finset.univ.filter (fun ω : Ω => e ω.out = b)).card := by
    have h := (Finset.even_sum_iff_even_card_odd (s := Finset.univ)
      (fun ω : Ω => 2 ^ (b - e ω.out))).not
    rw [Nat.not_even_iff_odd, Nat.not_even_iff_odd] at h
    have hfilter : (Finset.univ.filter (fun ω : Ω => Odd (2 ^ (b - e ω.out)))) =
        Finset.univ.filter (fun ω : Ω => e ω.out = b) := by
      refine Finset.filter_congr (fun ω _ => ?_)
      rw [← Nat.not_even_iff_odd, Nat.even_pow]
      have := he_le ω.out
      constructor
      · intro h2
        by_contra h3
        exact h2 ⟨even_two, by omega⟩
      · rintro h2 ⟨-, h3⟩
        exact h3 (by omega)
    rw [← hfilter]
    exact h.1 hS_odd
  let F : Ω → Set G := fun ω => {w | ∃ q ∈ Q, w = q * (ω.out : G) * q⁻¹}
  have hFinj : Function.Injective F := by
    intro ω ω' h
    have hmem : ((ω'.out : conjSet M z) : G) ∈ F ω := by
      rw [h]
      exact ⟨1, Q.one_mem, by group⟩
    obtain ⟨q, hq, hw⟩ := hmem
    have hout : ω'.out = (⟨q, hq⟩ : Q) • ω.out := Subtype.ext hw
    rw [← Quotient.out_eq ω, ← Quotient.out_eq ω']
    exact Quotient.sound (MulAction.orbitRel_apply.2
      (MulAction.mem_orbit_iff.2 ⟨(⟨q, hq⟩ : Q)⁻¹, by rw [hout, inv_smul_smul]⟩))
  have himage : extremalClasses M Q z (2 ^ b) = F '' {ω | e ω.out = b} := by
    ext O
    constructor
    · rintro ⟨y, hyQ, hyM, hyc, rfl⟩
      let x : conjSet M z := ⟨y, hyM⟩
      let ω : Ω := Quotient.mk _ x
      have hrel : ω.out ∈ MulAction.orbit Q x := by
        rw [← MulAction.orbitRel_apply]
        exact Quotient.exact (Quotient.out_eq ω)
      obtain ⟨q0, hq0⟩ := hrel
      refine ⟨ω, ?_, ?_⟩
      · have h1 : Nat.card (MulAction.stabilizer Q ω.out) =
            Nat.card (MulAction.stabilizer Q x) := by
          rw [← hq0, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
            Subgroup.card_map_of_injective (MulAut.conj q0).injective]
        rw [card_stabilizer_conjSetAction hQM, card_stabilizer_conjSetAction hQM, he] at h1
        show e ω.out = b
        exact Nat.pow_right_injective le_rfl (h1.trans hyc)
      · have hout : ((ω.out : conjSet M z) : G) = (q0 : G) * y * (q0 : G)⁻¹ := by
          rw [← hq0]
          rfl
        ext w
        constructor
        · rintro ⟨q, hq, rfl⟩
          exact ⟨q * q0, Q.mul_mem hq q0.2, by rw [hout]; group⟩
        · rintro ⟨q, hq, rfl⟩
          exact ⟨q * (q0 : G)⁻¹, Q.mul_mem hq (Q.inv_mem q0.2), by rw [hout]; group⟩
    · rintro ⟨ω, hω, rfl⟩
      have hc : Nat.card ↥(Q ⊓ centralizer ({((ω.out : conjSet M z) : G)} : Set G)) = 2 ^ b := by
        rw [he]
        exact congrArg _ hω
      exact ⟨ω.out, mem_of_card_eq hQM hQ hzM hz2 ω.out.2 hmax hc, ω.out.2, hc, rfl⟩
  rw [himage, Nat.card_image_of_injective hFinj, Set.coe_ofPred, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  exact hcardodd

end CFSG.EvenSporadicStandard.Fin76b

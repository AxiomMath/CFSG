module

public import CFSG.Holt.H78.SEModelFive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Radical

variable {Δ : Type}

@[expose] def seRadical (L : Subgroup (Equiv.Perm Δ)) (b : Δ) : Subgroup (Equiv.Perm Δ) :=
  Subgroup.closure {x | x ∈ L ∧ x b = b ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}

variable {L : Subgroup (Equiv.Perm Δ)} {b : Δ}

theorem seRadical_le : seRadical L b ≤ L :=
  (Subgroup.closure_le L).mpr fun _ hx => hx.1

theorem seRadical_le_stabilizer : seRadical L b ≤ stabilizer (Equiv.Perm Δ) b :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.2.1

theorem apply_eq_of_mem_seRadical {x : Equiv.Perm Δ} (hx : x ∈ seRadical L b) : x b = b :=
  seRadical_le_stabilizer hx

theorem mem_seRadical_of_pow_eq_one {x : Equiv.Perm Δ} (hxL : x ∈ L) (hxb : x b = b) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ seRadical L b :=
  Subgroup.subset_closure ⟨hxL, hxb, k, hk⟩

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {x : G} {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])

theorem conj_mem_seRadical {x : Equiv.Perm Δ} (hx : x ∈ Subgroup.normalizer (L : Set _))
    (hxb : x b = b) {r : Equiv.Perm Δ} (hr : r ∈ seRadical L b) : x * r * x⁻¹ ∈ seRadical L b := by
  have key : seRadical L b ≤ (seRadical L b).comap (MulAut.conj x).toMonoidHom := by
    rw [seRadical, Subgroup.closure_le]
    rintro y ⟨hyL, hyb, k, hk⟩
    refine mem_seRadical_of_pow_eq_one ((Subgroup.mem_normalizer_iff.mp hx y).mp hyL) ?_ (k := k) ?_
    · have hxb' : x⁻¹ b = b := by rw [Equiv.Perm.inv_eq_iff_eq, hxb]
      simp [Equiv.Perm.mul_apply, hxb', hyb, hxb]
    · rw [← map_pow, hk, map_one]
  exact key hr

end Radical

theorem rootCenter_map_of_injective {K K' : Type*} [Group K] [Group K'] (f : K →* K')
    (hf : Function.Injective f) (P : Subgroup K) :
    rootCenter (P.map f) = (rootCenter P).map f := by
  ext x
  simp only [mem_rootCenter_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hc⟩
    refine ⟨p, ⟨hp, fun p' hp' => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hc (f p') ⟨p', hp', rfl⟩
  · rintro ⟨p, ⟨hp, hc⟩, rfl⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    rintro _ ⟨p', hp', rfl⟩
    rw [← map_mul, hc p' hp', map_mul]

section Bridge

variable {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)} {n i e : ℕ}

namespace IsBenderAction

theorem seRadical_eq_map (hA : IsBenderAction ↥L Δ n i e) {b : Δ} {Q : Sylow 2 ↥L}
    (hQ : (Q : Subgroup ↥L) ≤ stabilizer ↥L b) :
    seRadical L b = (Q : Subgroup ↥L).map L.subtype := by
  apply le_antisymm
  · rw [seRadical, Subgroup.closure_le]
    rintro x ⟨hxL, hxb, k, hk⟩
    have hP : IsPGroup 2 (Subgroup.zpowers (⟨x, hxL⟩ : ↥L)) :=
      isPGroup_zpowers_of_pow_eq_one (k := k) (Subtype.ext (by simpa using hk))
    have hPb : Subgroup.zpowers (⟨x, hxL⟩ : ↥L) ≤ stabilizer ↥L b :=
      Subgroup.zpowers_le.mpr (mem_stabilizer_iff.mpr hxb)
    exact ⟨⟨x, hxL⟩, hA.le_sylow_of_isPGroup hQ hP hPb (Subgroup.mem_zpowers _), rfl⟩
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨q, hq⟩
    exact mem_seRadical_of_pow_eq_one q.2 (hQ hq) (k := k)
      (by simpa using congrArg Subtype.val (congrArg Subtype.val hk))

theorem rootCenter_seRadical_eq_map (hA : IsBenderAction ↥L Δ n i e) {b : Δ} {Q : Sylow 2 ↥L}
    (hQ : (Q : Subgroup ↥L) ≤ stabilizer ↥L b) :
    rootCenter (seRadical L b) = (rootCenter (Q : Subgroup ↥L)).map L.subtype := by
  rw [hA.seRadical_eq_map hQ, rootCenter_map_of_injective _ L.subtype_injective]

theorem card_seRadical (hA : IsBenderAction ↥L Δ n i e) (b : Δ) :
    Nat.card (seRadical L b) = (2 ^ n) ^ i := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  rw [hA.seRadical_eq_map hQ, Subgroup.card_map_of_injective L.subtype_injective, hc.card_eq]

theorem card_rootCenter_seRadical (hA : IsBenderAction ↥L Δ n i e) (b : Δ) :
    Nat.card (rootCenter (seRadical L b)) = 2 ^ n := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  rw [hA.rootCenter_seRadical_eq_map hQ, Subgroup.card_map_of_injective L.subtype_injective,
    hc.card_center]

theorem rootCenter_seRadical_eq_self (hA : IsBenderAction ↥L Δ n i e) (hi : i = 1) (b : Δ) :
    rootCenter (seRadical L b) = seRadical L b := by
  have : Finite ↥(seRadical L b) := inferInstance
  refine Subgroup.eq_of_le_of_card_ge (rootCenter_le _) ?_
  rw [hA.card_seRadical, hA.card_rootCenter_seRadical, hi, pow_one]

end IsBenderAction

namespace IsNaturalSE

variable {b : Δ}

theorem isPGroup_seRadical (hL : IsNaturalSE L) (b : Δ) : IsPGroup 2 (seRadical L b) := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  rw [hA.seRadical_eq_map hQ]
  exact Q.isPGroup'.map _

theorem mem_seRadical_iff (hL : IsNaturalSE L) {x : Equiv.Perm Δ} :
    x ∈ seRadical L b ↔ x ∈ L ∧ x b = b ∧ ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  refine ⟨fun hx => ⟨seRadical_le hx, apply_eq_of_mem_seRadical hx, ?_⟩,
    fun ⟨hxL, hxb, k, hk⟩ => mem_seRadical_of_pow_eq_one hxL hxb hk⟩
  obtain ⟨k, hk⟩ := hL.isPGroup_seRadical b ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_rootCenter_seRadical (hL : IsNaturalSE L) {x : Equiv.Perm Δ} (hxL : x ∈ L)
    (hxb : x b = b) (hx : x * x = 1) : x ∈ rootCenter (seRadical L b) := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  rw [hA.rootCenter_seRadical_eq_map hQ]
  have hxR : x ∈ seRadical L b := mem_seRadical_of_pow_eq_one hxL hxb (k := 1) (by
    rw [pow_one, sq, hx])
  rw [hA.seRadical_eq_map hQ] at hxR
  obtain ⟨y, hyQ, rfl⟩ := hxR
  by_cases hy1 : y = 1
  · rw [hy1, map_one]
    exact one_mem _
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by
    rw [sq]
    exact L.subtype_injective (by rw [map_mul, hx, map_one])) hy1
  exact ⟨y, BenderType.mem_rootCenter_of_mem_sylow hA.benderType Q hyQ hy2, rfl⟩

theorem mul_self_eq_one_of_mem_rootCenter (hL : IsNaturalSE L) {z : Equiv.Perm Δ}
    (hz : z ∈ rootCenter (seRadical L b)) : z * z = 1 := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  rw [hA.rootCenter_seRadical_eq_map hQ] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [← map_mul, hc.center_sq y hy, map_one]

theorem closure_seRadical_involutions (hL : IsNaturalSE L) :
    Subgroup.closure {x | x ∈ seRadical L b ∧ x * x = 1} = rootCenter (seRadical L b) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨hx, hx2⟩
    exact hL.mem_rootCenter_seRadical (seRadical_le hx) (apply_eq_of_mem_seRadical hx) hx2
  · intro z hz
    exact Subgroup.subset_closure ⟨rootCenter_le _ hz, hL.mul_self_eq_one_of_mem_rootCenter hz⟩

theorem mul_self_mem_rootCenter_seRadical (hL : IsNaturalSE L) {r : Equiv.Perm Δ}
    (hr : r ∈ seRadical L b) : r * r ∈ rootCenter (seRadical L b) := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  rw [hA.seRadical_eq_map hQ] at hr
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  rw [hA.rootCenter_seRadical_eq_map hQ, ← map_mul]
  refine ⟨r₀ * r₀, ?_, rfl⟩
  rcases hA.benderType.cases' with ⟨rfl, -, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, -, -⟩
  · obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
    have hZQ : rootCenter (Q : Subgroup ↥L) = Q := Subgroup.eq_of_le_of_card_ge
      (rootCenter_le _) (by rw [hc.card_center, hc.card_eq, pow_one])
    rw [hZQ]
    exact mul_mem hr₀ hr₀
  · exact hA.benderType.sq_mem_rootCenter_suzuki Q hr₀
  · exact hA.benderType.sq_mem_rootCenter_unitary Q hr₀

theorem eq_one_of_mem_seRadical (hL : IsNaturalSE L) {r : Equiv.Perm Δ}
    (hr : r ∈ seRadical L b) {c : Δ} (hcb : c ≠ b) (hrc : r c = c) : r = 1 := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  rw [hA.seRadical_eq_map hQ] at hr
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  rw [hA.eq_one_of_smul_eq hQ hr₀ hcb hrc, map_one]

theorem exists_mem_seRadical_apply_eq (hL : IsNaturalSE L) {c c' : Δ} (hc : c ≠ b)
    (hc' : c' ≠ b) : ∃ r ∈ seRadical L b, r c = c' := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  obtain ⟨p, hp, hpc⟩ := hA.exists_mem_smul_eq hQ hc hc'
  refine ⟨p, ?_, hpc⟩
  rw [hA.seRadical_eq_map hQ]
  exact ⟨p, hp, rfl⟩

end IsNaturalSE

omit [Finite Δ] in
theorem conj_mem_rootCenter_seRadical {b : Δ} {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hxb : x b = b)
    {z : Equiv.Perm Δ} (hz : z ∈ rootCenter (seRadical L b)) :
    x * z * x⁻¹ ∈ rootCenter (seRadical L b) := by
  rw [mem_rootCenter_iff] at hz ⊢
  have hxb' : x⁻¹ b = b := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hxb.symm
  refine ⟨conj_mem_seRadical hx hxb hz.1, fun p hp => ?_⟩
  have h1 := hz.2 (x⁻¹ * p * x⁻¹⁻¹) (conj_mem_seRadical (inv_mem hx) hxb' hp)
  calc p * (x * z * x⁻¹) = x * ((x⁻¹ * p * x⁻¹⁻¹) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * p * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
    _ = x * z * x⁻¹ * p := by group

end Bridge

section Normalizer

variable {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)}

namespace IsNaturalSE

theorem eq_one_of_commute (hL : IsNaturalSE L) {y : Equiv.Perm Δ}
    (hy : ∀ ℓ ∈ L, y * ℓ = ℓ * y) : y = 1 := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  ext δ
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer δ
  have hQy : (Q : Subgroup ↥L) ≤ stabilizer ↥L (y δ) := fun q hq => by
    rw [mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def]
    have h1 := congrArg (fun π : Equiv.Perm Δ => π δ) (hy q q.2)
    simp only [Equiv.Perm.mul_apply] at h1
    rw [← h1, show (q : Equiv.Perm Δ) δ = δ from hQ hq]
  obtain ⟨ω, -, huniq⟩ := hA.existsUnique_le_stabilizer Q
  rw [Equiv.Perm.one_apply, huniq _ hQy, huniq _ hQ]

theorem eq_of_conj_eq (hL : IsNaturalSE L) {x : Equiv.Perm Δ} {g : ↥L}
    (hg : ∀ ℓ : ↥L, x * ℓ * x⁻¹ = g * ℓ * (g : Equiv.Perm Δ)⁻¹) : x = g := by
  have h1 := hL.eq_one_of_commute (y := (g : Equiv.Perm Δ)⁻¹ * x) fun ℓ hℓ => by
    have h2 : x * ℓ * x⁻¹ = g * ℓ * (g : Equiv.Perm Δ)⁻¹ := hg ⟨ℓ, hℓ⟩
    calc (g : Equiv.Perm Δ)⁻¹ * x * ℓ = (g : Equiv.Perm Δ)⁻¹ * (x * ℓ * x⁻¹) * x := by group
      _ = ℓ * ((g : Equiv.Perm Δ)⁻¹ * x) := by rw [h2]; group
  calc x = g * ((g : Equiv.Perm Δ)⁻¹ * x) := by group
    _ = g := by rw [h1, mul_one]

theorem mem_of_conj_eq (hL : IsNaturalSE L) {x : Equiv.Perm Δ} {g : ↥L}
    (hg : ∀ ℓ : ↥L, x * ℓ * x⁻¹ = g * ℓ * (g : Equiv.Perm Δ)⁻¹) : x ∈ L := by
  rw [hL.eq_of_conj_eq hg]
  exact g.2

theorem not_inner (hL : IsNaturalSE L) {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hxL : x ∉ L) :
    ¬ ∃ g : ↥L, ∀ ℓ : ↥L, L.normalizerMonoidHom ⟨x, hx⟩ ℓ = g * ℓ * g⁻¹ := by
  rintro ⟨g, hg⟩
  exact hxL (hL.mem_of_conj_eq fun ℓ => by
    have := congrArg Subtype.val (hg ℓ)
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using this)

end IsNaturalSE

noncomputable def normalizerOuterHom (L : Subgroup (Equiv.Perm Δ)) :
    Subgroup.normalizer (L : Set (Equiv.Perm Δ)) →* Outer ↥L :=
  (QuotientGroup.mk' (inner ↥L)).comp L.normalizerMonoidHom

theorem IsNaturalSE.normalizerOuterHom_eq_one_iff (hL : IsNaturalSE L)
    (x : Subgroup.normalizer (L : Set (Equiv.Perm Δ))) :
    normalizerOuterHom L x = 1 ↔ (x : Equiv.Perm Δ) ∈ L := by
  rw [normalizerOuterHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact hL.mem_of_conj_eq (g := g) fun ℓ => by
      have := congrArg Subtype.val (DFunLike.congr_fun hg ℓ)
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this.symm
  · intro hxL
    refine ⟨⟨x, hxL⟩, MulEquiv.ext fun ℓ => Subtype.ext ?_⟩
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]

theorem IsNaturalSE.mem_rootCenter_seRadical_of_commute (hL : IsNaturalSE L) {b : Δ}
    {x : Equiv.Perm Δ} (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hxR : ∀ r ∈ seRadical L b, x * r = r * x) : x ∈ rootCenter (seRadical L b) := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  have hQR : ∀ q ∈ (Q : Subgroup ↥L), (q : Equiv.Perm Δ) ∈ seRadical L b := fun q hq => by
    rw [hA.seRadical_eq_map hQ]
    exact ⟨q, hq, rfl⟩
  obtain ⟨r, hr, hσr⟩ := hA.benderType.lemma_3_6_a Q (L.normalizerMonoidHom ⟨x, hx⟩)
    fun q hq => Subtype.ext (by
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [hxR _ (hQR q hq), mul_inv_cancel_right])
  have hxr : x = r := hL.eq_of_conj_eq fun ℓ => by
    have := congrArg Subtype.val (hσr ℓ)
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  rw [hxr, hA.rootCenter_seRadical_eq_map hQ]
  exact ⟨r, hr, rfl⟩

theorem IsNaturalSE.exists_conj_eq (hL : IsNaturalSE L) {b c : Δ} (hbc : b ≠ c)
    {z z' : Equiv.Perm Δ} (hz : z ∈ rootCenter (seRadical L b)) (hz1 : z ≠ 1)
    (hz' : z' ∈ rootCenter (seRadical L b)) (hz'1 : z' ≠ 1) :
    ∃ d ∈ L, d b = b ∧ d c = c ∧ d * z * d⁻¹ = z' := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  obtain ⟨t, ht, htb⟩ := hA.exists_involution_smul_eq hbc
  have hc := hA.benderCore hQ ht (htb.trans_ne hbc.symm)
  rw [hA.rootCenter_seRadical_eq_map hQ] at hz hz'
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨y', hy', rfl⟩ := hz'
  have hy1 : y ≠ 1 := fun h => hz1 (by rw [h, map_one])
  have hy'1 : y' ≠ 1 := fun h => hz'1 (by rw [h, map_one])
  obtain ⟨d, ⟨hd, hdy⟩, -⟩ :=
    (hA.stabilizer_inf_decomposition hQ hbc ht htb).2.2.2.1 y hy hy1 y' hy' hy'1
  have hdD : d ∈ stabilizer ↥L b ⊓ stabilizer ↥L c := by
    rw [hA.stabilizer_inf_eq_cartan hQ ht htb] at hd ⊢
    exact hc.commutator_cartan_le hd
  refine ⟨((d⁻¹ : ↥L) : Equiv.Perm Δ), (d⁻¹ : ↥L).2, (inv_mem hdD).1, (inv_mem hdD).2, ?_⟩
  simp [hdy]

theorem IsNaturalSE.eq_bot_or_eq_rootCenter (hL : IsNaturalSE L) {b c : Δ} (hbc : b ≠ c)
    {W : Subgroup (Equiv.Perm Δ)} (hW : W ≤ rootCenter (seRadical L b))
    (hinv : ∀ d ∈ L, d b = b → d c = c → ∀ w ∈ W, d * w * d⁻¹ ∈ W) :
    W = ⊥ ∨ W = rootCenter (seRadical L b) := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  obtain ⟨⟨w, hw⟩, hw1⟩ := W.ne_bot_iff_exists_ne_one.mp hbot
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  refine Or.inr (le_antisymm hW fun z hz => ?_)
  by_cases hz1 : z = 1
  · rw [hz1]
    exact one_mem W
  obtain ⟨d, hdL, hdb, hdc, rfl⟩ := hL.exists_conj_eq hbc (hW hw) hw1' hz hz1
  exact hinv d hdL hdb hdc w hw

end Normalizer

section Irreducible

namespace IsBenderAction

variable {X : Type*} [Group X] [Finite X] {Ω : Type*} [MulAction X Ω] {n i e : ℕ}

theorem eq_rootCenter_or_eq_of_suzuki (hA : IsBenderAction X Ω n 2 e) {α β : Ω} (hαβ : α ≠ β)
    {Q : Sylow 2 X} (hQ : (Q : Subgroup X) ≤ stabilizer X α) {W : Subgroup X}
    (hZW : rootCenter (Q : Subgroup X) ≤ W) (hWQ : W ≤ Q)
    (hinv : ∀ d ∈ stabilizer X α ⊓ stabilizer X β, ∀ w ∈ W, d * w * d⁻¹ ∈ W) :
    W = rootCenter (Q : Subgroup X) ∨ W = Q := by
  classical
  by_cases hle : W ≤ rootCenter (Q : Subgroup X)
  · exact Or.inl (le_antisymm hle hZW)
  right
  obtain ⟨w, hw, hwZ⟩ := Set.not_subset.mp hle
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  have he : e = 1 := by
    rcases hA.benderType.cases' with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ <;> omega
  set D := stabilizer X α ⊓ stabilizer X β with hD
  set Z := rootCenter (Q : Subgroup X) with hZ
  have hDcard : Nat.card D = 2 ^ n - 1 := by rw [hA.card_stabilizer_inf hαβ, he, mul_one]
  have hDB : ∀ d ∈ D, d ∈ borel (Q : Subgroup X) := fun d hd => (hA.mem_borel_iff hQ).mpr hd.1
  have hconjZ : ∀ d ∈ D, ∀ z ∈ Z, d * z * d⁻¹ ∈ Z := fun d hd z hz =>
    conj_mem_rootCenter (hDB d hd) hz
  have hwQ : w ∈ (Q : Subgroup X) := hWQ hw
  have hne1 : ∀ d ∈ D, d * w * d⁻¹ ∉ Z := fun d hd h => hwZ (by
    have := hconjZ d⁻¹ (inv_mem hd) _ h
    rwa [show d⁻¹ * (d * w * d⁻¹) * d⁻¹⁻¹ = w by group] at this)
  have key : ∀ d ∈ D, ∀ d' ∈ D, (d * w * d⁻¹)⁻¹ * (d' * w * d'⁻¹) ∈ Z → d = d' := by
    intro d hd d' hd' h
    have huD : d⁻¹ * d' ∈ D := mul_mem (inv_mem hd) hd'
    have h1 : w⁻¹ * ((d⁻¹ * d') * w * (d⁻¹ * d')⁻¹) ∈ Z := by
      have := hconjZ d⁻¹ (inv_mem hd) _ h
      rwa [show d⁻¹ * ((d * w * d⁻¹)⁻¹ * (d' * w * d'⁻¹)) * d⁻¹⁻¹ =
        w⁻¹ * ((d⁻¹ * d') * w * (d⁻¹ * d')⁻¹) by group] at this
    have hc2 := (mem_rootCenter_iff.mp h1).2 w hwQ
    have h2 : (d⁻¹ * d') * w * (d⁻¹ * d')⁻¹ * w⁻¹ ∈ Z := by
      have e1 : (d⁻¹ * d') * w * (d⁻¹ * d')⁻¹ * w⁻¹ =
          w * (w⁻¹ * ((d⁻¹ * d') * w * (d⁻¹ * d')⁻¹)) * w⁻¹ := by group
      rw [e1, hc2, show w⁻¹ * (d⁻¹ * d' * w * (d⁻¹ * d')⁻¹) * w * w⁻¹ =
        w⁻¹ * (d⁻¹ * d' * w * (d⁻¹ * d')⁻¹) by group]
      exact h1
    by_contra hne
    have hu1 : d⁻¹ * d' ≠ 1 := fun h' => hne (inv_mul_eq_one.mp h')
    exact hwZ (hA.mem_rootCenter_of_commutator_mem hQ hαβ huD hu1 hwQ h2)
  let F : Option D → ↥W ⧸ Z.subgroupOf W := fun o =>
    o.elim (QuotientGroup.mk 1) fun d =>
      (QuotientGroup.mk ⟨d * w * d⁻¹, hinv d d.2 w hw⟩ : ↥W ⧸ Z.subgroupOf W)
  have hF : Function.Injective F := by
    rintro (_ | ⟨d, hd⟩) (_ | ⟨d', hd'⟩) h
    · rfl
    · exfalso
      have h' : (QuotientGroup.mk 1 : ↥W ⧸ Z.subgroupOf W) =
          QuotientGroup.mk ⟨d' * w * d'⁻¹, hinv d' hd' w hw⟩ := h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
      exact hne1 d' hd' (by simpa using h')
    · exfalso
      have h' : (QuotientGroup.mk ⟨d * w * d⁻¹, hinv d hd w hw⟩ : ↥W ⧸ Z.subgroupOf W) =
          QuotientGroup.mk 1 := h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
      exact hne1 d hd (by simpa [mul_assoc] using Z.inv_mem h')
    · have h' : (QuotientGroup.mk ⟨d * w * d⁻¹, hinv d hd w hw⟩ : ↥W ⧸ Z.subgroupOf W) =
          QuotientGroup.mk ⟨d' * w * d'⁻¹, hinv d' hd' w hw⟩ := h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
      have := key d hd d' hd' (by simpa using h')
      subst this
      rfl
  have h1 := Nat.card_le_card_of_injective F hF
  rw [Finite.card_option, hDcard] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf W)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv, hc.card_center] at h2
  refine Subgroup.eq_of_le_of_card_ge hWQ ?_
  have := hA.four_le_q
  rw [hc.card_eq, h2, sq]
  exact Nat.mul_le_mul_right _ (by omega)

end IsBenderAction

variable {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)} {n i e : ℕ}

theorem IsBenderAction.eq_rootCenter_or_eq_seRadical (hA : IsBenderAction ↥L Δ n i e)
    {b c : Δ} (hbc : b ≠ c) {W : Subgroup (Equiv.Perm Δ)}
    (hZW : rootCenter (seRadical L b) ≤ W) (hWR : W ≤ seRadical L b)
    (hinv : ∀ d ∈ L, d b = b → d c = c → ∀ w ∈ W, d * w * d⁻¹ ∈ W) :
    W = rootCenter (seRadical L b) ∨ W = seRadical L b := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  obtain ⟨t, ht, htb⟩ := hA.exists_involution_smul_eq hbc
  have hc := hA.benderCore hQ ht (htb.trans_ne hbc.symm)
  set W₀ : Subgroup ↥L := W.comap L.subtype with hW₀
  have hWmap : W = W₀.map L.subtype := by
    rw [hW₀, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact (inf_eq_right.mpr (hWR.trans seRadical_le)).symm
  have hZ₀ : rootCenter (Q : Subgroup ↥L) ≤ W₀ := fun z hz =>
    hZW (by rw [hA.rootCenter_seRadical_eq_map hQ]; exact ⟨z, hz, rfl⟩)
  have hW₀Q : W₀ ≤ (Q : Subgroup ↥L) := fun w hw => by
    have h1 : (w : Equiv.Perm Δ) ∈ seRadical L b := hWR hw
    rw [hA.seRadical_eq_map hQ] at h1
    obtain ⟨q, hq, hqw⟩ := h1
    rwa [← L.subtype_injective hqw]
  have hD : ∀ d ∈ stabilizer ↥L b ⊓ stabilizer ↥L c, ∀ w ∈ W₀, d * w * d⁻¹ ∈ W₀ :=
    fun d hd w hw => by
      have := hinv d d.2 hd.1 hd.2 w hw
      rw [hW₀, Subgroup.mem_comap]
      simpa using this
  have key : W₀ = rootCenter (Q : Subgroup ↥L) ∨ W₀ = Q := by
    rcases hA.benderType.cases' with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · have hZQ : rootCenter (Q : Subgroup ↥L) = Q := Subgroup.eq_of_le_of_card_ge
        (rootCenter_le _) (by rw [hc.card_center, hc.card_eq, pow_one])
      exact Or.inl (le_antisymm (hW₀Q.trans hZQ.ge) hZ₀)
    · exact hA.eq_rootCenter_or_eq_of_suzuki hbc hQ hZ₀ hW₀Q hD
    · refine hA.benderType.irreducible_unitary Q ht hc.not_mem W₀ hZ₀ hW₀Q fun d hd w hw => ?_
      rw [← hA.stabilizer_inf_eq_cartan hQ ht htb] at hd
      exact hD d hd w hw
  rcases key with h | h
  · left
    rw [hWmap, h, hA.rootCenter_seRadical_eq_map hQ]
  · right
    rw [hWmap, h, hA.seRadical_eq_map hQ]

theorem IsNaturalSE.eq_rootCenter_or_eq_seRadical (hL : IsNaturalSE L) {b c : Δ} (hbc : b ≠ c)
    {W : Subgroup (Equiv.Perm Δ)} (hZW : rootCenter (seRadical L b) ≤ W)
    (hWR : W ≤ seRadical L b) (hinv : ∀ d ∈ L, d b = b → d c = c → ∀ w ∈ W, d * w * d⁻¹ ∈ W) :
    W = rootCenter (seRadical L b) ∨ W = seRadical L b := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  exact hA.eq_rootCenter_or_eq_seRadical hbc hZW hWR hinv

end Irreducible

section Cyclic

theorem eq_of_mul_self_eq_one_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {a b : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite G
  by_contra hab
  have h := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) two_pos
  have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ.filter fun g => g ^ 2 = 1 := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl <;> simp [sq, ha, hb]
  have hcard : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha1, Ne.symm hb1]), Finset.card_pair hab]
  have := Finset.card_le_card hsub
  omega

variable {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)} {n i e : ℕ}

omit [Finite Δ] in
theorem normal_subgroupOf_of_le_normalizer {S : Subgroup (Equiv.Perm Δ)}
    (hSN : S ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) : (L.subgroupOf S).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hSN g.2) x).mp hx⟩

theorem IsNaturalSE.ker_normalizerOuterHom_comp (hL : IsNaturalSE L)
    {S : Subgroup (Equiv.Perm Δ)} (hSN : S ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) :
    ((normalizerOuterHom L).comp (Subgroup.inclusion hSN)).ker = L.subgroupOf S := by
  ext s
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hL.normalizerOuterHom_eq_one_iff,
    Subgroup.mem_subgroupOf]
  rfl

theorem IsNaturalSE.isCyclic_range_normalizerOuterHom_comp (hL : IsNaturalSE L)
    {S : Subgroup (Equiv.Perm Δ)} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) :
    IsCyclic ((normalizerOuterHom L).comp (Subgroup.inclusion hSN)).range := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  set f := (normalizerOuterHom L).comp (Subgroup.inclusion hSN)
  have hR2 : IsPGroup 2 f.range := hS2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hR2.exists_le_sylow
  have : IsCyclic ↥(P : Subgroup (Outer ↥L)) := hA.benderType.isCyclic_sylow_outer P
  exact isCyclic_of_injective (Subgroup.inclusion hP) (Subgroup.inclusion_injective hP)

theorem IsNaturalSE.isCyclic_quotient (hL : IsNaturalSE L) {S : Subgroup (Equiv.Perm Δ)}
    (hS2 : IsPGroup 2 S) (hSN : S ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    [(L.subgroupOf S).Normal] : IsCyclic (↥S ⧸ L.subgroupOf S) := by
  set f := (normalizerOuterHom L).comp (Subgroup.inclusion hSN)
  have := hL.isCyclic_range_normalizerOuterHom_comp hS2 hSN
  have e₁ : ↥S ⧸ L.subgroupOf S ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq (hL.ker_normalizerOuterHom_comp hSN).symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  exact isCyclic_of_injective e₁.toMonoidHom e₁.injective

theorem IsNaturalSE.isCyclic_of_isPGroup (hL : IsNaturalSE L) {a b : Δ} (hab : a ≠ b)
    {S : Subgroup (Equiv.Perm Δ)} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hSa : ∀ s ∈ S, s a = a)
    (hSb : ∀ s ∈ S, s b = b) : IsCyclic S := by
  obtain ⟨n, i, e, hA⟩ := hL.exists_isBenderAction
  set f := (normalizerOuterHom L).comp (Subgroup.inclusion hSN)
  have := hL.isCyclic_range_normalizerOuterHom_comp hS2 hSN
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, hL.ker_normalizerOuterHom_comp hSN, eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs
    have hmem : (⟨s, hs⟩ : ↥L) ∈ stabilizer ↥L a ⊓ stabilizer ↥L b := ⟨hSa s s.2, hSb s s.2⟩
    obtain ⟨k, hk⟩ := hS2 s
    have h1 : orderOf (⟨s, hs⟩ : ↥L) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using congrArg Subtype.val hk))
    have h2 := Subgroup.orderOf_dvd_natCard _ hmem
    have h3 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 ((Nat.coprime_two_left.mpr
        (hA.odd_card_stabilizer_inf hab)).pow_left k)) h2
    rw [orderOf_eq_one_iff] at h3
    exact Subgroup.mem_bot.mpr (Subtype.ext (congrArg (fun y : ↥L => (y : Equiv.Perm Δ)) h3))
  exact isCyclic_of_injective f.rangeRestrict fun a b h =>
    hinj (by simpa using congrArg Subtype.val h)

theorem IsNaturalSE.mul_inv_mem_of_isPGroup (hL : IsNaturalSE L) {S : Subgroup (Equiv.Perm Δ)}
    (hS2 : IsPGroup 2 S) (hSN : S ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    {x y : Equiv.Perm Δ} (hxS : x ∈ S) (hyS : y ∈ S) (hx : x * x = 1) (hy : y * y = 1)
    (hxL : x ∉ L) (hyL : y ∉ L) : x * y⁻¹ ∈ L := by
  set f := (normalizerOuterHom L).comp (Subgroup.inclusion hSN) with hf
  have := hL.isCyclic_range_normalizerOuterHom_comp hS2 hSN
  have hfin : Finite (MulAut ↥L) :=
    Finite.of_injective (fun φ : MulAut ↥L => (φ : ↥L → ↥L)) DFunLike.coe_injective
  have hker : ∀ s : ↥S, f s = 1 ↔ (s : Equiv.Perm Δ) ∈ L := fun s => by
    rw [← MonoidHom.mem_ker, hL.ker_normalizerOuterHom_comp hSN, Subgroup.mem_subgroupOf]
  have hsq : ∀ s : ↥S, (s : Equiv.Perm Δ) * s = 1 →
      f.rangeRestrict s * f.rangeRestrict s = 1 := fun s hs => by
    rw [← map_mul, show s * s = 1 from Subtype.ext hs, map_one]
  have hne : ∀ s : ↥S, (s : Equiv.Perm Δ) ∉ L → f.rangeRestrict s ≠ 1 := fun s hs h => by
    apply hs
    rw [← hker s]
    exact congrArg Subtype.val h
  have heq := eq_of_mul_self_eq_one_of_isCyclic (hsq ⟨x, hxS⟩ hx) (hsq ⟨y, hyS⟩ hy)
    (hne ⟨x, hxS⟩ hxL) (hne ⟨y, hyS⟩ hyL)
  have h1 : f (⟨x, hxS⟩ * (⟨y, hyS⟩ : ↥S)⁻¹) = 1 := by
    rw [map_mul, map_inv, show f ⟨x, hxS⟩ = f ⟨y, hyS⟩ from congrArg Subtype.val heq,
      mul_inv_cancel]
  simpa using (hker _).mp h1

end Cyclic

end CFSG.Holt.H78

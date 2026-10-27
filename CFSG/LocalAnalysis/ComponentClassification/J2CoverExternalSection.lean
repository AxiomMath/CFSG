module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferDihedral

public section

universe u

namespace CFSG.ComponentClassification.J2Cover.External

open Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

section Fixed

variable {H : Type u} [Group H] {L : Subgroup H} {t : L}

theorem map_centralizer_eq [L.Normal] (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* P)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {p : H} (g : P)
    (hα : ∀ l : L, (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹) (π l) =
      π (MulAut.conjNormal p l)) {v : L} (hv : (v : H) * p * (v : H)⁻¹ = t * p) :
    ((centralizer {p}).subgroupOf L).map π = fixD.map (MulAut.conj g).toMonoidHom := by
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htH : (t : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ ht2
  set α := MulAut.conj g * betaAut * (MulAut.conj g)⁻¹ with hαdef
  have hF : FixedCommutingProduct.fixedSubgroup α = fixSub α := rfl
  obtain ⟨δ, hδs, hδk⟩ : ∃ δ : FixedCommutingProduct.fixedSubgroup α →* zpowers (t : H),
      Function.Surjective δ ∧ δ.ker.map (FixedCommutingProduct.fixedSubgroup α).subtype =
        ((centralizer {p}).subgroupOf L).map π :=
    ⟨_, CentralCover.fixedLiftObstruction_surjective_of_conj π hπ hker htH p α hα hv,
      CentralCover.map_ker_fixedLiftObstruction π hπ hker htH p α hα⟩
  have hcardF : Nat.card (FixedCommutingProduct.fixedSubgroup α) = 336 := by
    rw [hF, hαdef]
    exact card_fixSub_conj_beta g
  have hcardT : Nat.card (zpowers (t : H)) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht]
  have hcardK : Nat.card δ.ker = 168 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective δ hδs).toEquiv, hcardF,
      hcardT] at h1
    omega
  have hle : ⁅FixedCommutingProduct.fixedSubgroup α, FixedCommutingProduct.fixedSubgroup α⁆ ≤
      δ.ker.map (FixedCommutingProduct.fixedSubgroup α).subtype := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.map_mono (Abelianization.commutator_subset_ker δ)
  have heq : δ.ker.map (FixedCommutingProduct.fixedSubgroup α).subtype =
      ⁅FixedCommutingProduct.fixedSubgroup α, FixedCommutingProduct.fixedSubgroup α⁆ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcardK, hF, hαdef,
      commutator_fixSub_conj_beta, card_fixD_map_conj]
  rw [← hδk, heq, hF, hαdef, commutator_fixSub_conj_beta]

theorem t_mem_centralizer [L.Normal] (ht : orderOf t = 2) (hZ : center L = zpowers t) (p : H) :
    t ∈ (centralizer {p}).subgroupOf L := by
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htH : (t : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ ht2
  rw [mem_subgroupOf, mem_centralizer_singleton_iff]
  exact (mem_center_iff.mp htH p).symm

@[expose] noncomputable def restrictHom (π : L →* P) {p : H} (g : P)
    (hmap : ((centralizer {p}).subgroupOf L).map π = fixD.map (MulAut.conj g).toMonoidHom) :
    (centralizer {p}).subgroupOf L →* fixD :=
  (conjFixDEquiv g).toMonoidHom.comp ((π.comp ((centralizer {p}).subgroupOf L).subtype).codRestrict
    _ fun x => by rw [← hmap]; exact ⟨x, x.2, rfl⟩)

theorem conj_restrictHom (π : L →* P) {p : H} (g : P)
    (hmap : ((centralizer {p}).subgroupOf L).map π = fixD.map (MulAut.conj g).toMonoidHom)
    (x : (centralizer {p}).subgroupOf L) :
    g * (restrictHom π g hmap x : P) * g⁻¹ = π x :=
  conj_conjFixDEquiv g _

theorem fixed_section [Finite H] [L.Normal] (hlift : J2LiftOrders.{u})
    (hLq : CFSG.Assembly.IsQuasisimple L) (ht : orderOf t = 2) (hZ : center L = zpowers t)
    (π : L →* P) (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {p : H} (g : P)
    (hmap : ((centralizer {p}).subgroupOf L).map π = fixD.map (MulAut.conj g).toMonoidHom) :
    zpowers t ⊔ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ =
      (centralizer {p}).subgroupOf L ∧
    zpowers t ⊓ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ = ⊥ ∧
    (∃ e : (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) ≃*
        fixD.map (MulAut.conj g).toMonoidHom, ∀ a, (e a : P) = π a) ∧
    ⁅⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
      ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆⁆ =
      ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ := by
  set K := (centralizer {p}).subgroupOf L with hKdef
  have htK : t ∈ K := t_mem_centralizer ht hZ p
  have htZ : t ∈ center L := by
    rw [hZ]
    exact mem_zpowers t
  set z : K := ⟨t, htK⟩ with hzdef
  set ρ := restrictHom π g hmap with hρdef
  have hρz : ∀ x : K, g * (ρ x : P) * g⁻¹ = π x := conj_restrictHom π g hmap
  have hρ : CentralCover.IsCentralDoubleExt ρ z := by
    refine ⟨fun d => ?_, ?_, ?_, ?_⟩
    · have hd : g * (d : P) * g⁻¹ ∈ fixD.map (MulAut.conj g).toMonoidHom := ⟨d, d.2, rfl⟩
      rw [← hmap] at hd
      obtain ⟨x, hx, hxd⟩ := hd
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      have h1 := hρz ⟨x, hx⟩
      rw [show π (⟨x, hx⟩ : K) = π x from rfl, hxd] at h1
      simpa using h1
    · rw [mem_center_iff]
      intro k
      exact Subtype.ext (mem_center_iff.mp htZ k)
    · rw [← Subgroup.orderOf_coe]
      exact ht
    · ext x
      rw [MonoidHom.mem_ker]
      constructor
      · intro hx
        have h1 := hρz x
        rw [hx, OneMemClass.coe_one, mul_one, mul_inv_cancel] at h1
        have h2 : (x : L) ∈ π.ker := h1.symm
        rw [hker, mem_zpowers_iff] at h2
        obtain ⟨k, hk⟩ := h2
        exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow, hk])⟩
      · intro hx
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
        have h1 := hρz (z ^ k)
        have h2 : π ((z ^ k : K) : L) = 1 := by
          rw [SubgroupClass.coe_zpow, ← MonoidHom.mem_ker, hker]
          exact zpow_mem (mem_zpowers t) k
        rw [h2] at h1
        apply Subtype.ext
        have : (ρ (z ^ k) : P) = g⁻¹ * (g * (ρ (z ^ k) : P) * g⁻¹) * g := by group
        rw [this, h1]
        simp
  have hlifts : ∀ x : K, orderOf (ρ x) = 2 → orderOf x = 2 := by
    intro x hx
    have hx' : orderOf (π x) = 2 := by
      rw [← hρz x, ← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
    have hmem : π x ∈ fixD.map (MulAut.conj g).toMonoidHom := ⟨ρ x, (ρ x).2, hρz x⟩
    have h11 := fixCount_of_mem_fixD_map_conj g hmem hx'
    rw [← Subgroup.orderOf_coe]
    exact (hlift hLq ht hZ π hπ hker).2.1 x hx' h11
  have : Group.IsPerfect fixD := Subgroup.isPerfect_iff.2 fixD_perfect
  obtain ⟨W, r, s, hW, hr, hs, -⟩ := exists_sylow_fixD
  have hr4 : orderOf r = 2 ^ 2 := by
    rw [← Subgroup.orderOf_coe, hr, orderOf_elemR]
    norm_num
  have hs2 : orderOf s = 2 := by
    rw [← Subgroup.orderOf_coe, hs, orderOf_elemS]
  have hsr : s ∉ zpowers r := by
    intro h
    have h1 := Subgroup.mem_map_of_mem (P.subtype.comp fixD.subtype) h
    rw [MonoidHom.map_zpowers] at h1
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hr, hs] at h1
    exact permS_not_mem_zpowers h1
  have hrs : s * r * s⁻¹ = r⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hr, hs]
    exact elemS_conj_elemR
  obtain ⟨hinf, hsup, hperf, ⟨e, he⟩, -⟩ :=
    CentralCover.central_double_extension_splits_over_dihedral_sylow W hW hr4 hs2 hsr hrs hρ
      hlifts
  have hmapA : (commutator K).map K.subtype = ⁅K, K⁆ := Subgroup.map_subtype_commutator K
  have hmapz : (zpowers z).map K.subtype = zpowers t := by
    rw [MonoidHom.map_zpowers]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmapA, ← hmapz, ← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · rw [← hmapA, ← hmapz, ← Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, hinf,
      Subgroup.map_bot]
  · let eA : (⁅K, K⁆ : Subgroup L) ≃* commutator K :=
      (MulEquiv.subgroupCongr hmapA.symm).trans
        ((commutator K).equivMapOfInjective K.subtype K.subtype_injective).symm
    have heA : ∀ a, ((eA a : K) : L) = a := by
      intro a
      have := ((commutator K).equivMapOfInjective K.subtype K.subtype_injective).apply_symm_apply
        (MulEquiv.subgroupCongr hmapA.symm a)
      exact congrArg Subtype.val this
    refine ⟨(eA.trans e).trans (conjFixDEquiv g).symm, fun a => ?_⟩
    simp only [MulEquiv.trans_apply]
    have h1 : (conjFixDEquiv g).symm (e (eA a)) = (conjFixDEquiv g).symm (ρ (eA a)) := by
      rw [he]
    rw [h1]
    have h2 := conj_conjFixDEquiv g ((conjFixDEquiv g).symm (ρ (eA a)))
    rw [MulEquiv.apply_symm_apply] at h2
    rw [← h2, hρz, heA]
  · rw [← hmapA, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperf]

end Fixed

section Conjugator

theorem inv_conj_of_conj {G : Type*} [Group G] {t p v : G} (htH : t ∈ center G)
    (hv : v * p * v⁻¹ = t * p) : v⁻¹ * p * v = t⁻¹ * p := by
  have hc := mem_center_iff.mp htH
  have h1 : p = v⁻¹ * (t * p) * v := by
    rw [← hv]
    group
  have h2 : t * (v⁻¹ * p * v) = v⁻¹ * (t * p) * v := by
    rw [← mul_assoc v⁻¹, hc v⁻¹]
    group
  calc v⁻¹ * p * v = t⁻¹ * (t * (v⁻¹ * p * v)) := by group
    _ = t⁻¹ * p := by rw [h2, ← h1]

theorem conj_comm_of_conj {G : Type*} [Group G] {t p v : G} (htH : t ∈ center G)
    (htt : t * t = 1) (hv : v * p * v⁻¹ = t * p) : p * v * p⁻¹ = v * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  calc p * v * p⁻¹ = v * (v⁻¹ * p * v) * p⁻¹ := by group
    _ = v * t⁻¹ := by rw [inv_conj_of_conj htH hv]; group
    _ = v * t := by rw [htinv]

theorem conj_mem_centralizer {G : Type*} [Group G] {t p v : G} (htH : t ∈ center G)
    (htt : t * t = 1) (hv : v * p * v⁻¹ = t * p) {k : G} (hk : k ∈ centralizer {p}) :
    v * k * v⁻¹ ∈ centralizer {p} := by
  have hci := mem_center_iff.mp (inv_mem htH)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [mem_centralizer_singleton_iff] at hk ⊢
  have h2 := inv_conj_of_conj htH hv
  calc v * k * v⁻¹ * p = v * k * (v⁻¹ * p * v) * v⁻¹ := by group
    _ = t⁻¹ * (v * (k * p) * v⁻¹) := by
        rw [h2, ← mul_assoc (v * k) t⁻¹ p, hci (v * k)]
        group
    _ = t⁻¹ * (v * p * v⁻¹ * (v * k * v⁻¹)) := by rw [hk]; group
    _ = p * (v * k * v⁻¹) := by
        rw [hv, htinv]
        calc t * (t * p * (v * k * v⁻¹)) = t * t * p * (v * k * v⁻¹) := by group
          _ = p * (v * k * v⁻¹) := by rw [htt, one_mul]

end Conjugator

theorem center_eq_bot_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : center G' = ⊥) : center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ center G' := by
    rw [mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [h, mem_bot, MulEquiv.map_eq_one_iff] at hz'
  exact mem_bot.2 hz'

end CFSG.ComponentClassification.J2Cover.External

namespace CFSG.ComponentClassification.J2Cover

open Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms External

theorem ctss_j2_actual_double_cover_external_conjugacy_and_exact_fixed_section_of_liftOrders
    (hlift : J2LiftOrders.{u}) {H : Type u} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hLq : CFSG.Assembly.IsQuasisimple L) {t : L} (ht : orderOf t = 2)
    (hZ : center L = zpowers t) (π : L →* P) (hπ : Function.Surjective π)
    (hker : π.ker = zpowers t) (hCL : centralizer (L : Set H) = zpowers (t : H)) :
    (∀ x y : H, x ∉ L → orderOf x = 2 → y ∉ L → orderOf y = 2 →
      ∃ l : L, (l : H) * x * (l : H)⁻¹ = y) ∧
    ∀ p : H, p ∉ L → orderOf p = 2 → ∀ α : MulAut P,
      (∀ l : L, α (π l) = π (MulAut.conjNormal p l)) →
      Nat.card (fixSub α) = 336 ∧
      ⁅⁅fixSub α, fixSub α⁆, ⁅fixSub α, fixSub α⁆⁆ = ⁅fixSub α, fixSub α⁆ ∧
      Nat.card (⁅fixSub α, fixSub α⁆ : Subgroup P) = 168 ∧
      centralizer ((⁅fixSub α, fixSub α⁆ : Subgroup P) : Set P) ⊓ fixSub α = ⊥ ∧
      zpowers t ⊔ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ =
        (centralizer {p}).subgroupOf L ∧
      zpowers t ⊓ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ = ⊥ ∧
      t ∈ center L ∧
      (∃ e : (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) ≃*
          (⁅fixSub α, fixSub α⁆ : Subgroup P), ∀ a, (e a : P) = π a) ∧
      ⁅⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
          ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆⁆ =
        ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ ∧
      Nat.card (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ :
        Subgroup L) = 168 ∧
      center (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ :
        Subgroup L) = ⊥ ∧
      Nat.card (Outer (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ :
        Subgroup L)) ∣ 2 ∧
      ∃ c ∈ fixSub α, c ∉ ⁅fixSub α, fixSub α⁆ ∧ orderOf c = 2 ∧
        Models.fixCount (c : Equiv.Perm (Fin 315)) = 15 ∧
        ∀ v : L, π v = c → v ^ 2 = t ∧ p * (v : H) * p⁻¹ = v * t ∧
          (∀ a ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
            v * a * v⁻¹ ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆) ∧
          (¬ ∃ a ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
            ∀ x ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
              v * x * v⁻¹ = a * x * a⁻¹) ∧
          (v : H) * p * (v : H)⁻¹ = t * p := by
  have hkerZ : π.ker = center L := hker.trans hZ.symm
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htH : (t : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ ht2
  have htt : (t : H) * t = 1 := by rw [← Subgroup.coe_mul, ← sq, ht2, OneMemClass.coe_one]
  have htZ : t ∈ center L := by
    rw [hZ]
    exact mem_zpowers t
  have hCL' : centralizer (L : Set H) ≤ L := by
    rw [hCL, zpowers_le]
    exact t.2
  obtain ⟨-, hconj⟩ := external_involution_conjugacy hlift hLq ht hZ π hπ hker hCL
  refine ⟨hconj, fun p hpL hp α hα => ?_⟩
  have hθ : CentralCover.fullAction π hπ hkerZ p = α := by
    ext q
    obtain ⟨l, rfl⟩ := hπ q
    rw [CentralCover.fullAction_apply, hα]
  obtain ⟨hα2, hαo⟩ := fullAction_outer_involution π hπ hkerZ hCL' hpL hp
  rw [hθ] at hα2 hαo
  obtain ⟨g, rfl⟩ := exists_conj_beta_of_outer hα2 hαo
  obtain ⟨v₀, hv₀⟩ := hπ (g * elemC * g⁻¹)
  obtain ⟨-, hv₀p, -⟩ := lift_conj_elemC hlift hLq ht hZ π hπ hker hCL hpL hp g hα hv₀
  have hmap := map_centralizer_eq ht hZ π hπ hker g hα hv₀p
  obtain ⟨hsup, hinf, ⟨e, he⟩, hperf⟩ := fixed_section hlift hLq ht hZ π hπ hker g hmap
  have hD := commutator_fixSub_conj_beta g
  obtain ⟨hc1, hc2, hc3, hc4⟩ := conj_elemC g
  have hbot : centralizer ((⁅fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹),
      fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹)⁆ : Subgroup P) : Set P) ⊓
        fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹) = ⊥ := by
    rw [hD, fixSub_conj_beta]
    exact centralizer_fixD_map_conj_inf g
  let e' := e.trans (MulEquiv.subgroupCongr hD.symm)
  have he' : ∀ a, (e' a : P) = π a := fun a => he a
  refine ⟨card_fixSub_conj_beta g, by rw [hD]; exact fixD_map_conj_perfect g,
    by rw [hD]; exact card_fixD_map_conj g, hbot, hsup, hinf, htZ, ⟨e', he'⟩, hperf,
    by rw [Nat.card_congr e.toEquiv, card_fixD_map_conj], center_eq_bot_of_mulEquiv e
    (center_fixD_map_conj g), by
      rw [Nat.card_congr (equivalence e).toEquiv]
      exact card_outer_fixD_map_conj g,
    g * elemC * g⁻¹, hc1, hc2, hc3, hc4, fun v hv => ?_⟩
  obtain ⟨hv2, hvp, -⟩ := lift_conj_elemC hlift hLq ht hZ π hπ hker hCL hpL hp g hα hv
  refine ⟨hv2, conj_comm_of_conj htH htt hvp, fun a ha => ?_, ?_, hvp⟩
  ·
    have hK : ((centralizer {p}).subgroupOf L).map (MulAut.conj v).toMonoidHom ≤
        (centralizer {p}).subgroupOf L := by
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hk
      show _ ∈ (centralizer {p}).subgroupOf L
      rw [mem_subgroupOf]
      simpa using conj_mem_centralizer htH htt hvp hk
    have h1 : (MulAut.conj v).toMonoidHom a ∈ (⁅(centralizer {p}).subgroupOf L,
        (centralizer {p}).subgroupOf L⁆).map (MulAut.conj v).toMonoidHom :=
      mem_map_of_mem _ ha
    rw [Subgroup.map_commutator] at h1
    simpa using Subgroup.commutator_mono hK hK h1
  ·
    rintro ⟨a, ha, hall⟩
    have hpa : π a ∈ ⁅fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹),
        fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹)⁆ := by
      rw [← he' ⟨a, ha⟩]
      exact (e' ⟨a, ha⟩).2
    have hcent : (π a)⁻¹ * π v ∈ centralizer ((⁅fixSub (MulAut.conj g * betaAut *
        (MulAut.conj g)⁻¹), fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹)⁆ :
          Subgroup P) : Set P) ⊓
          fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹) := by
      refine mem_inf.2 ⟨mem_centralizer_iff.2 fun d hd => ?_,
        mul_mem (inv_mem (Subgroup.commutator_le_self _ hpa)) (hv ▸ hc1)⟩
      obtain ⟨x, hx⟩ := e'.surjective ⟨d, hd⟩
      have hdx : d = π x := by
        rw [← he' x, hx]
      have heq := congrArg π (hall x x.2)
      simp only [map_mul, map_inv] at heq
      rw [hdx]
      calc π x * ((π a)⁻¹ * π v) = (π a)⁻¹ * (π a * π x * (π a)⁻¹) * π v := by group
        _ = (π a)⁻¹ * (π v * π x * (π v)⁻¹) * π v := by rw [heq]
        _ = (π a)⁻¹ * π v * π x := by group
    rw [hbot, mem_bot, inv_mul_eq_one] at hcent
    exact hc2 (by rw [← hv, ← hcent]; exact hpa)

end CFSG.ComponentClassification.J2Cover

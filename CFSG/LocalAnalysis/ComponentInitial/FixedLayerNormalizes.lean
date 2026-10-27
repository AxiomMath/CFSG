module

public import CFSG.LocalAnalysis.ComponentInitial.PerfectFixedCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.LocalCores
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem fittingSubgroup_eq_closure (G : Type*) [Group G] :
    CFSG.fittingSubgroup G = closure (⋃ N ∈ {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N},
      (N : Set G)) := by
  refine le_antisymm (sSup_le fun N hN => ?_) ((closure_le _).2 ?_)
  · exact fun x hx => subset_closure (Set.mem_biUnion hN hx)
  · intro x hx
    obtain ⟨N, hN, hxN⟩ := Set.mem_iUnion₂.1 hx
    exact (le_sSup hN : N ≤ CFSG.fittingSubgroup G) hxN

theorem map_center_layer_le_fittingSubgroup :
    (center (CFSG.layer G)).map (CFSG.layer G).subtype ≤ CFSG.fittingSubgroup G := by
  set E := CFSG.layer G
  have : E.Characteristic := layer_characteristic
  have hEn : E.Normal := inferInstance
  set Z := (center E).map E.subtype with hZ
  have hZn : Z.Normal := by
    refine ⟨fun z hz g => ?_⟩
    rw [hZ, mem_map_center_iff] at hz ⊢
    refine ⟨hEn.conj_mem z hz.1 g, fun e he => ?_⟩
    have he' : g⁻¹ * e * g ∈ E := by simpa using hEn.conj_mem e he g⁻¹
    have h := hz.2 _ he'
    calc e * (g * z * g⁻¹) = g * ((g⁻¹ * e * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * e * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * e := by group
  have : IsMulCommutative Z := ⟨⟨fun a b => Subtype.ext
    (((mem_map_center_iff.1 a.2).2 b (mem_map_center_iff.1 b.2).1).symm)⟩⟩
  have hZnil : Group.IsNilpotent Z := inferInstance
  exact le_sSup ⟨hZn, hZnil⟩

theorem exists_noncentral_fixed_mod_center [Finite G] {K : Subgroup G}
    (hK : CFSG.IsQuasisimple K) {t : G} (htt : t * t = 1) (htK : t ∈ normalizer (K : Set G)) :
    ∃ k ∈ K, k ∉ (center K).map K.subtype ∧
      k⁻¹ * (t⁻¹ * k * t) ∈ (center K).map K.subtype := by
  classical
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hmem : ∀ k ∈ K, t⁻¹ * k * t ∈ K := fun k hk => by
    have h := (mem_normalizer_iff.1 htK k).1 hk
    rw [htinv] at h ⊢
    exact h
  let ψ : K →* K :=
    { toFun := fun k => ⟨t⁻¹ * k * t, hmem k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hψ : ∀ k : K, ((ψ k : K) : G) = t⁻¹ * k * t := fun _ => rfl
  have hψψ : ∀ k, ψ (ψ k) = k := fun k => Subtype.ext (by
    rw [hψ, hψ, htinv]
    calc t * (t * (k : G) * t) * t = (t * t) * k * (t * t) := by group
      _ = k := by rw [htt, one_mul, mul_one])
  have hψc : center K ≤ (center K).comap ψ := by
    intro z hz
    rw [mem_comap, mem_center_iff]
    intro g
    have h := mem_center_iff.1 hz (ψ g)
    calc g * ψ z = ψ (ψ g) * ψ z := by rw [hψψ]
      _ = ψ (ψ g * z) := by rw [map_mul]
      _ = ψ (z * ψ g) := by rw [h]
      _ = ψ z * g := by rw [map_mul, hψψ]
  let φ : K ⧸ center K →* K ⧸ center K := QuotientGroup.map (center K) (center K) ψ hψc
  have hφ : ∀ k : K, φ (k : K ⧸ center K) = ((ψ k : K) : K ⧸ center K) := fun _ => rfl
  have hinvol : Function.Involutive φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k => rw [hφ, hφ, hψψ]
  have hnf : ¬ MonoidHom.FixedPointFree φ := by
    intro hfpf
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact hab (hfpf.commute_all_of_involutive hinvol a b).eq
  simp only [MonoidHom.FixedPointFree, not_forall] at hnf
  obtain ⟨q, hq, hq1⟩ := hnf
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨k, k.2, fun hk => hq1 ?_, ?_⟩
  · obtain ⟨z, hz, hzk⟩ := hk
    rw [QuotientGroup.eq_one_iff]
    rwa [← Subtype.ext hzk]
  · rw [hφ, QuotientGroup.eq] at hq
    have h := inv_mem hq
    rw [mul_inv_rev, inv_inv] at h
    exact ⟨_, h, by simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hψ]⟩

theorem mem_centralizer_of_mem_centralizer_conjSub {a e : G} (hae : a * e = e * a)
    {L : Subgroup G} (h : e ∈ centralizer (conjSub a L : Set G)) : e ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff] at h ⊢
  intro y hy
  have hy' := h (a * y * a⁻¹) ⟨y, hy, rfl⟩
  have hea : a⁻¹ * e * a = e := by rw [mul_assoc, ← hae, inv_mul_cancel_left]
  calc y * e = y * (a⁻¹ * e * a) := by rw [hea]
    _ = a⁻¹ * (a * y * a⁻¹ * e) * a := by group
    _ = a⁻¹ * (e * (a * y * a⁻¹)) * a := by rw [hy']
    _ = (a⁻¹ * e * a) * y := by group
    _ = e * y := by rw [hea]

theorem mem_normalizer_of_conjSub_eq {a : G} {K : Subgroup G} (h : conjSub a K = K) :
    a ∈ normalizer (K : Set G) := by
  refine mem_normalizer_of_conjSub_le h.le ?_
  conv_lhs => rw [← h]
  rw [conjSub_inv_conjSub]

theorem perfect_involution_fixed_layer_centralizer_normalizes_components {H : Type*} [Group H]
    [Finite H] {t : H} (ht : orderOf t = 2) {A : Subgroup H}
    (hAt : A ≤ centralizer ({t} : Set H)) (hA : Group.IsPerfect A)
    (hAF : ⁅A, CFSG.fittingSubgroup H⁆ = ⊥)
    (hAE : ⁅A, CFSG.layer H ⊓ centralizer ({t} : Set H)⁆ = ⊥) :
    ∀ K : Subgroup H, CFSG.IsComponent K → A ≤ normalizer (K : Set H) := by
  classical
  intro K hK
  set E := CFSG.layer H with hE
  have : E.Characteristic := layer_characteristic
  have hEn : E.Normal := inferInstance
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hAta : ∀ a ∈ A, a * t = t * a := fun a ha =>
    (mem_centralizer_iff.1 (hAt ha) t rfl).symm
  have hAZ : ⁅A, (center E).map E.subtype⁆ = ⊥ :=
    le_bot_iff.1 (hAF ▸ commutator_mono le_rfl map_center_layer_le_fittingSubgroup)
  have htE : t ∈ normalizer (E : Set H) := by rw [normalizer_eq_top]; exact mem_top t
  obtain ⟨P, hPdef, hAP⟩ := unique_perfect_fixed_central_quotient_centralization (E := E)
    (A := A) htE (fun a ha => mem_inf.2 ⟨by rw [normalizer_eq_top]; exact mem_top a,
      hAt ha⟩) hA hAZ hAE
  have hcomm : ∀ a ∈ A, ∀ e ∈ E, e⁻¹ * (t⁻¹ * e * t) ∈ (center E).map E.subtype →
      a * e = e * a := by
    intro a ha e he hz
    have heP : e ∈ (P : Set H) := by rw [hPdef]; exact ⟨he, hz⟩
    exact (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hAP ha) e heP).symm
  have hdist : ∀ L M : Subgroup H, CFSG.IsComponent L → CFSG.IsComponent M → L ≠ M →
      ∀ x ∈ L, ∀ y ∈ M, x * y = y * x := by
    intro L M hL hM hLM x hx y hy
    rcases distinct_components_commute hL hM with h | h
    · exact absurd h hLM
    · exact (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h hx) y hy).symm
  have hcompconj : ∀ g : H, ∀ L : Subgroup H, CFSG.IsComponent L →
      CFSG.IsComponent (conjSub g L) := fun g L hL =>
    isComponent_map_of_isComponent (MulAut.conj g) hL
  by_cases htK : t ∈ normalizer (K : Set H)
  ·
    obtain ⟨k, hkK, hkZ, hkfix⟩ := exists_noncentral_fixed_mod_center hK.1 htt htK
    have hkC : k ∉ centralizer (K : Set H) := fun h => hkZ (mem_map_center_iff.2
      ⟨hkK, fun e he => (mem_centralizer_iff.1 h e he)⟩)
    intro a ha
    have hka := hcomm a ha k (component_le_layer hK hkK) (center_component_le_center_layer hK hkfix)
    by_contra hne
    have hLK : conjSub a K ≠ K := fun h => hne (mem_normalizer_of_conjSub_eq h)
    apply hkC
    refine mem_centralizer_of_mem_centralizer_conjSub hka (mem_centralizer_iff.2 fun y hy => ?_)
    exact (hdist K _ hK (hcompconj a K hK) hLK.symm k hkK y hy).symm
  ·
    set K'' := conjSub t K with hK''
    have hK''c : CFSG.IsComponent K'' := hcompconj t K hK
    have hK''ne : K'' ≠ K := fun h => htK (mem_normalizer_of_conjSub_eq h)
    obtain ⟨k, hkK, hkC⟩ : ∃ k ∈ K, k ∉ centralizer (K : Set H) := by
      obtain ⟨a, b, hab⟩ := hK.1.2.2
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      refine ⟨x, x.2, fun h => hab ?_⟩
      have hxy : (x : H) * y = y * x := (mem_centralizer_iff.1 h y y.2).symm
      have hxy' : x * y = y * x := Subtype.ext hxy
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy']
    have hkt : t * k * t⁻¹ ∈ K'' := ⟨k, hkK, rfl⟩
    have hkk : k * (t * k * t⁻¹) = (t * k * t⁻¹) * k := hdist K K'' hK hK''c hK''ne.symm k hkK _ hkt
    obtain ⟨e, he⟩ : ∃ e, e = k * (t * k * t⁻¹) := ⟨_, rfl⟩
    have hefix : t⁻¹ * e * t = e := by
      rw [he, hkk, htinv]
      calc t * (t * k * t * k) * t = (t * t) * k * t * (k * t) := by group
        _ = k * t * k * t := by rw [htt, one_mul, ← mul_assoc]
        _ = t * k * t * k := ?_
      have h2 := hkk
      rw [htinv] at h2
      calc k * t * k * t = k * (t * k * t) := by group
        _ = t * k * t * k := h2
    have heE : e ∈ E := he ▸ mul_mem (component_le_layer hK hkK) (component_le_layer hK''c hkt)
    have hae : ∀ a ∈ A, a * e = e * a := fun a ha => hcomm a ha e heE (by
      rw [hefix, inv_mul_cancel]
      exact one_mem _)
    have heK : e ∉ centralizer (K : Set H) := by
      intro h
      apply hkC
      rw [mem_centralizer_iff] at h ⊢
      intro y hy
      have hy1 := h y hy
      have hy2 : y * (t * k * t⁻¹) = (t * k * t⁻¹) * y :=
        hdist K K'' hK hK''c hK''ne.symm y hy _ hkt
      apply mul_right_cancel (b := t * k * t⁻¹)
      calc y * k * (t * k * t⁻¹) = y * e := by rw [he]; group
        _ = e * y := hy1
        _ = k * ((t * k * t⁻¹) * y) := by rw [he]; group
        _ = k * y * (t * k * t⁻¹) := by rw [← hy2]; group
    have heL : ∀ L : Subgroup H, CFSG.IsComponent L → L ≠ K → L ≠ K'' →
        e ∈ centralizer (L : Set H) := by
      intro L hL hLK hLK''
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := hdist K L hK hL hLK.symm k hkK y hy
      have h2 := hdist K'' L hK''c hL hLK''.symm _ hkt y hy
      rw [he]
      calc y * (k * (t * k * t⁻¹)) = (y * k) * (t * k * t⁻¹) := by group
        _ = (k * y) * (t * k * t⁻¹) := by rw [h1]
        _ = k * (y * (t * k * t⁻¹)) := by group
        _ = k * ((t * k * t⁻¹) * y) := by rw [h2]
        _ = k * (t * k * t⁻¹) * y := by group
    have hmove : ∀ a ∈ A, conjSub a K = K ∨ conjSub a K = K'' := by
      intro a ha
      by_contra h
      push Not at h
      exact heK (mem_centralizer_of_mem_centralizer_conjSub (hae a ha)
        (heL _ (hcompconj a K hK) h.1 h.2))
    have hK''a : ∀ a ∈ A, conjSub a K'' = conjSub t (conjSub a K) := fun a ha => by
      rw [hK'', ← conjSub_mul, ← conjSub_mul, hAta a ha]
    have htK'' : conjSub t K'' = K := by
      rw [hK'', ← conjSub_mul, htt, conjSub, show (MulAut.conj (1 : H)).toMonoidHom =
        MonoidHom.id H from by ext; simp, Subgroup.map_id]
    have hmul : ∀ a ∈ A, ∀ b ∈ A,
        (conjSub (a * b) K = K ↔ (conjSub a K = K ↔ conjSub b K = K)) := by
      intro a ha b hb
      rw [conjSub_mul]
      rcases hmove b hb with hbK | hbK
      · rw [hbK]
        simp
      · rw [hbK, hK''a a ha]
        rcases hmove a ha with haK | haK
        · rw [haK, ← hK'']
          simp [hK''ne]
        · rw [haK, htK'']
          simp [hK''ne]
    have hinv : ∀ a ∈ A, (conjSub a⁻¹ K = K ↔ conjSub a K = K) := by
      intro a _
      constructor
      · intro h
        conv_lhs => rw [← h]
        rw [conjSub_conjSub_inv]
      · intro h
        conv_lhs => rw [← h]
        rw [conjSub_inv_conjSub]
    have hcfix : ∀ a ∈ A, ∀ b ∈ A, conjSub ⁅a, b⁆ K = K := by
      intro a ha b hb
      rw [commutatorElement_def]
      have hab := mul_mem ha hb
      have haba := mul_mem hab (inv_mem ha)
      rw [hmul _ haba _ (inv_mem hb), hmul _ hab _ (inv_mem ha), hmul _ ha _ hb,
        hinv a ha, hinv b hb]
      tauto
    have hAA : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.1 hA
    rw [← hAA, commutator_le]
    intro a ha b hb
    exact mem_normalizer_of_conjSub_eq (hcfix a ha b hb)

end CFSG.LocalAnalysis.ComponentInitial

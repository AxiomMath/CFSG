module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Fusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1SigmaRTypeD

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

@[expose] def e1Act (A B v : Fin 64) : Fin 64 :=
  c3Mul (c3Mul (if v.val / 32 % 2 = 0 then 0 else A) (if v.val / 8 % 2 = 0 then 0 else c3Mul A 40))
    (if v.val / 2 % 2 = 0 then 0 else B)

theorem e1Act_facts : c3Mul 32 40 = 8 ∧ c3Mul 32 2 = 34 ∧
    ∀ v : Fin 64, e1E v → e1Act 32 2 v = v := by decide

theorem e1_kernel_reps : (∀ r : Fin 64, (r = 0 ∨ r = 1 ∨ r = 20 ∨ r = 21) → e1R r) ∧
    c3Conj 0 32 = 32 ∧ c3Conj 0 2 = 2 ∧ c3Conj 1 32 = 8 ∧ c3Conj 1 2 = 2 ∧
    c3Conj 20 32 = 32 ∧ c3Conj 20 2 = 42 ∧ c3Conj 21 32 = 8 ∧ c3Conj 21 2 = 42 ∧
    c3Mul 32 40 = 8 ∧ c3Mul 2 40 = 42 := by decide

theorem conj_mem_centralizer_of_mem_normalizer {G : Type*} [Group G] {E : Subgroup G} {n c : G}
    (hn : n ∈ Subgroup.normalizer (E : Set G)) (hc : c ∈ Subgroup.centralizer (E : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : n⁻¹ * s * n⁻¹⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) s).mp hs
  rw [inv_inv] at hs'
  have h := hc _ hs'
  calc s * (n * c * n⁻¹) = n * ((n⁻¹ * s * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * s * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * s := by group

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem mem_e1EBar_gens : (u : J ⧸ Subgroup.center J) ∈ e1EBar (Subgroup.center J) u m y x ∧
    (y : J ⧸ Subgroup.center J) ∈ e1EBar (Subgroup.center J) u m y x ∧
    caseC3Word (Subgroup.center J) u m y x 40 ∈ e1EBar (Subgroup.center J) u m y x := by
  have hb := d.caseC3BCD
  refine ⟨?_, ?_, hb.forty_mem_e1EBar⟩
  · rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x)]
    exact hb.caseC3Word_mem_e1EBar_iff.mpr e1E_gens.1
  · rw [← CaseC3BCD.caseC3Word_two (Z := Subgroup.center J) (u := u) (m := m) (x := x)]
    exact hb.caseC3Word_mem_e1EBar_iff.mpr e1E_gens.2.2.1

theorem normalizer_e1EBar_le :
    Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) ≤
      Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} := fun c hc => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := d.caseC3BCD.conj_forty_of_normalizes_e1EBar fun t ht =>
    (Subgroup.mem_normalizer_iff.mp hc t).mp ht
  calc c * caseC3Word (Subgroup.center J) u m y x 40 =
        c * caseC3Word (Subgroup.center J) u m y x 40 * c⁻¹ * c := by group
    _ = _ := by rw [h]

theorem map_le_normalizer_e1EBar : (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) ≤
    Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) :=
  fun _ hs => mem_normalizer_of_forall_conj_mem fun _ ht => d.caseC3BCD.conj_mem_e1EBar hs ht

theorem e1EBar_facts : Nat.card (e1EBar (Subgroup.center J) u m y x) = 8 ∧
    (∀ s ∈ e1EBar (Subgroup.center J) u m y x, s * s = 1) ∧
    (∀ s ∈ e1EBar (Subgroup.center J) u m y x, ∀ t ∈ e1EBar (Subgroup.center J) u m y x,
      s * t = t * s) ∧
    ∀ s ∈ e1EBar (Subgroup.center J) u m y x, CaseC3.Genuine (Subgroup.center J) s ↔
      s = 1 ∨ s = caseC3Word (Subgroup.center J) u m y x 40 := by
  have hb := d.caseC3BCD
  refine ⟨hb.card_e1EBar, fun s hs => hb.mul_self_of_mem_e1EBar hs,
    fun s hs t ht => hb.commute_of_mem_e1EBar hs ht, fun s hs => ⟨fun hg => ?_, ?_⟩⟩
  · by_contra h
    push Not at h
    exact (hb.not_genuine_of_mem_e1EBar hs h.1 h.2).1 hg
  · rintro (rfl | rfl)
    exacts [⟨1, QuotientGroup.mk_one _, mul_one 1⟩, hb.genuine_forty]

theorem conj_mod_forty_of_mem_e1RBar {r c : J ⧸ Subgroup.center J}
    (hr : r ∈ e1RBar (Subgroup.center J) u m y x)
    (hc : c ∈ Subgroup.centralizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)))
    {s : J ⧸ Subgroup.center J} (hs : s ∈ e1EBar (Subgroup.center J) u m y x) :
    r * c * s * (r * c)⁻¹ = s ∨
      r * c * s * (r * c)⁻¹ = s * caseC3Word (Subgroup.center J) u m y x 40 := by
  have hb := d.caseC3BCD
  have hcs : c * s * c⁻¹ = s := by
    rw [← Subgroup.mem_centralizer_iff.mp hc s hs]
    group
  have hrz : r * caseC3Word (Subgroup.center J) u m y x 40 =
      caseC3Word (Subgroup.center J) u m y x 40 * r :=
    (hb.forall_commute_e1RBar_iff hb.forty_mem_e1RBar).mpr (Or.inr rfl) r hr |>.symm
  rw [show r * c * s * (r * c)⁻¹ = r * (c * s * c⁻¹) * r⁻¹ by group, hcs]
  rcases hb.commute_or_of_mem_e1RBar hr (hb.e1EBar_le_e1RBar hs) with h | h
  · left
    rw [h]
    group
  · right
    rw [h, mul_assoc s r, hrz]
    group

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem mem_normalizer_of_conj_mem_map {g : J ⧸ Subgroup.center J}
    (hg : g ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})
    (hgS : ∀ s ∈ e1EBar (Subgroup.center J) u m y x,
      g * s * g⁻¹ ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))) :
    g ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) := by
  have hb := d.caseC3BCD
  have hgz := conj_self_of_mem_centralizer_singleton hg
  set A := (e1EBar (Subgroup.center J) u m y x).map (MulAut.conj g).toMonoidHom with hA
  have hmemA : ∀ s ∈ e1EBar (Subgroup.center J) u m y x, g * s * g⁻¹ ∈ A := fun s hs =>
    ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have hAE : A = e1EBar (Subgroup.center J) u m y x := by
    refine hb.eq_e1EBar_of_typeD htype ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply] using hgS s hs
    · rw [← hgz]
      exact hmemA _ hb.forty_mem_e1EBar
    · rw [hA, Subgroup.card_map_of_injective (MulAut.conj g).injective, hb.card_e1EBar]
    · rintro _ ⟨s, hs, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ by group,
        hb.mul_self_of_mem_e1EBar hs]
      group
    · rintro _ ⟨s, hs, rfl⟩ hs1 hsz hgen
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hs1 hsz hgen
      refine (hb.not_genuine_of_mem_e1EBar hs (fun h => hs1 (by rw [h]; group))
        (fun h => hsz (by rw [h, hgz]))).1 ?_
      have h' := CaseC3.genuine_conj _ hgen g
      rwa [show g⁻¹ * (g * s * g⁻¹) * g = s by group] at h'
  exact mem_normalizer_of_forall_conj_mem fun s hs => hAE ▸ hmemA s hs

theorem exists_normalizer_conj_two :
    ∃ n ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)),
      n * (u : J ⧸ Subgroup.center J) * n⁻¹ = (y : J ⧸ Subgroup.center J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb := d.caseC3BCD
  obtain ⟨huE, hyE, hzE⟩ := d.mem_e1EBar_gens
  obtain ⟨h₀, hh₀, hh₀u⟩ := d.exists_centralizer_conj_two htype
  have hh₀z := conj_self_of_mem_centralizer_singleton hh₀
  set E := e1EBar (Subgroup.center J) u m y x with hE
  set zb := caseC3Word (Subgroup.center J) u m y x 40 with hzb
  set D := Subgroup.centralizer {zb} ⊓ Subgroup.centralizer {(y : J ⧸ Subgroup.center J)} with hD
  have hED : E ≤ D := fun s hs => ⟨Subgroup.mem_centralizer_singleton_iff.mpr
    (hb.commute_of_mem_e1EBar hs hzE), Subgroup.mem_centralizer_singleton_iff.mpr
      (hb.commute_of_mem_e1EBar hs hyE)⟩
  have hconjc : ∀ {s a : J ⧸ Subgroup.center J}, s * a = a * s →
      h₀ * s * h₀⁻¹ * (h₀ * a * h₀⁻¹) = h₀ * a * h₀⁻¹ * (h₀ * s * h₀⁻¹) := fun {s a} h => by
    rw [show h₀ * s * h₀⁻¹ * (h₀ * a * h₀⁻¹) = h₀ * (s * a) * h₀⁻¹ by group, h]
    group
  have hFD : E.map (MulAut.conj h₀).toMonoidHom ≤ D := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · have h := hconjc (hb.commute_of_mem_e1EBar hs hzE)
      rwa [hh₀z] at h
    · have h := hconjc (hb.commute_of_mem_e1EBar hs huE)
      rwa [hh₀u] at h
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hb.card_e1EBar]; norm_num)
  obtain ⟨P, hP⟩ := (hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hED).symm).exists_le_sylow
  obtain ⟨k, -, hk⟩ := exists_conj_mem_sylow_of_le P (X := ⊤) le_top le_top
    ((hE2.map _).of_equiv (Subgroup.subgroupOfEquivOfLe hFD).symm)
  set S'' := S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J))
  have hS'' : (S'' : Subgroup (J ⧸ Subgroup.center J)) =
      (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) := Sylow.coe_mapSurjective _ _
  obtain ⟨k', hk', hk'P⟩ := exists_conj_mem_sylow_of_le S''
    (hS''.symm ▸ d.map_le_centralizer_forty) ((Subgroup.map_subtype_le _).trans inf_le_left)
    (P.isPGroup'.map D.subtype)
  have hk'N := d.mem_normalizer_of_conj_mem_map htype hk' fun s hs =>
    hS'' ▸ hk'P s (Subgroup.mem_map_of_mem D.subtype (hP (Subgroup.mem_subgroupOf.mpr hs) :
      (⟨s, hED hs⟩ : D) ∈ (P : Subgroup D)))
  have hN := d.mem_normalizer_of_conj_mem_map htype (g := k' * k * h₀)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hk' k.2.1) hh₀) fun s hs => by
      have hf : (⟨h₀ * s * h₀⁻¹, hFD ⟨s, hs, by simp [MulAut.conj_apply]⟩⟩ : D) ∈
          (E.map (MulAut.conj h₀).toMonoidHom).subgroupOf D :=
        Subgroup.mem_subgroupOf.mpr ⟨s, hs, by simp [MulAut.conj_apply]⟩
      have h1 := hk'P _ (Subgroup.mem_map_of_mem D.subtype (hk _ hf))
      rw [hS''] at h1
      convert h1 using 1
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  refine ⟨k * h₀, ?_, ?_⟩
  · have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hk'N) hN
    rwa [show k'⁻¹ * (k' * (k : J ⧸ Subgroup.center J) * h₀) = k * h₀ by group] at h
  · rw [show (k : J ⧸ Subgroup.center J) * h₀ * (u : J ⧸ Subgroup.center J) * (k * h₀)⁻¹ =
      k * (h₀ * (u : J ⧸ Subgroup.center J) * h₀⁻¹) * (k : J ⧸ Subgroup.center J)⁻¹ by group,
      hh₀u]
    exact conj_self_of_mem_centralizer_singleton k.2.2

theorem exists_normalizer_conj_of_mem_e1EBar {s : J ⧸ Subgroup.center J}
    (hs : s ∈ e1EBar (Subgroup.center J) u m y x) (hs1 : s ≠ 1)
    (hsz : s ≠ caseC3Word (Subgroup.center J) u m y x 40) :
    ∃ n ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)),
      n * (u : J ⧸ Subgroup.center J) * n⁻¹ = s := by
  rcases d.caseC3BCD.exists_conj_of_mem_e1EBar hs hs1 hsz with ⟨a, ha, has⟩ | ⟨a, ha, has⟩
  · exact ⟨a, d.map_le_normalizer_e1EBar ha, has⟩
  · obtain ⟨n, hn, hnu⟩ := d.exists_normalizer_conj_two htype
    refine ⟨a * n, Subgroup.mul_mem _ (d.map_le_normalizer_e1EBar ha) hn, ?_⟩
    rw [show a * n * (u : J ⧸ Subgroup.center J) * (a * n)⁻¹ =
      a * (n * (u : J ⧸ Subgroup.center J) * n⁻¹) * a⁻¹ by group, hnu, has]

omit htype in
theorem conj_caseC3Word_of_e1E {g : J ⧸ Subgroup.center J} {wa we : Fin 64}
    (hA : g * (u : J ⧸ Subgroup.center J) * g⁻¹ = caseC3Word (Subgroup.center J) u m y x wa)
    (hB : g * (y : J ⧸ Subgroup.center J) * g⁻¹ = caseC3Word (Subgroup.center J) u m y x we)
    (hgz : g * caseC3Word (Subgroup.center J) u m y x 40 * g⁻¹ =
      caseC3Word (Subgroup.center J) u m y x 40) {v : Fin 64} (hv : e1E v) :
    g * caseC3Word (Subgroup.center J) u m y x v * g⁻¹ =
      caseC3Word (Subgroup.center J) u m y x (e1Act wa we v) := by
  have hb := d.caseC3BCD
  have key : ∀ (p : Prop) [Decidable p] (w W : Fin 64),
      g * caseC3Word (Subgroup.center J) u m y x w * g⁻¹ =
        caseC3Word (Subgroup.center J) u m y x W →
      g * caseC3Word (Subgroup.center J) u m y x (if p then 0 else w) * g⁻¹ =
        caseC3Word (Subgroup.center J) u m y x (if p then 0 else W) := by
    intro p _ w W h
    split_ifs
    · rw [CaseC3BCD.caseC3Word_zero]
      group
    · exact h
  have h32 : g * caseC3Word (Subgroup.center J) u m y x 32 * g⁻¹ =
      caseC3Word (Subgroup.center J) u m y x wa := by
    rw [CaseC3BCD.caseC3Word_thirtytwo]
    exact hA
  have h8 : g * caseC3Word (Subgroup.center J) u m y x 8 * g⁻¹ =
      caseC3Word (Subgroup.center J) u m y x (c3Mul wa 40) := by
    rw [← e1Act_facts.1, ← hb.caseC3Word_mul, ← hb.caseC3Word_mul, ← h32]
    nth_rewrite 2 [← hgz]
    group
  have h2 : g * caseC3Word (Subgroup.center J) u m y x 2 * g⁻¹ =
      caseC3Word (Subgroup.center J) u m y x we := by
    rw [CaseC3BCD.caseC3Word_two]
    exact hB
  conv_lhs => rw [e1E_eq_mul v hv, ← hb.caseC3Word_mul, ← hb.caseC3Word_mul]
  unfold e1Act
  rw [← hb.caseC3Word_mul, ← hb.caseC3Word_mul, ← key _ 32 wa h32, ← key _ 8 _ h8,
    ← key _ 2 we h2]
  group

omit htype in
theorem exists_mem_e1RBar_of_conj_mod_forty {n : J ⧸ Subgroup.center J}
    (hn : n ∈ Subgroup.normalizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)))
    (hnE : ∀ s ∈ e1EBar (Subgroup.center J) u m y x, n * s * n⁻¹ = s ∨
      n * s * n⁻¹ = s * caseC3Word (Subgroup.center J) u m y x 40) :
    ∃ r ∈ e1RBar (Subgroup.center J) u m y x, r⁻¹ * n ∈
      Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) := by
  have hb := d.caseC3BCD
  have hnz := conj_self_of_mem_centralizer_singleton (d.normalizer_e1EBar_le hn)
  have hu : (u : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 32 :=
    CaseC3BCD.caseC3Word_thirtytwo.symm
  have hy : (y : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 2 :=
    CaseC3BCD.caseC3Word_two.symm
  obtain ⟨hR, h0a, h0e, h1a, h1e, h20a, h20e, h21a, h21e, h8, h42⟩ := e1_kernel_reps
  have hnw : ∀ t : Fin 64, e1E t → n * caseC3Word (Subgroup.center J) u m y x t * n⁻¹ =
      caseC3Word (Subgroup.center J) u m y x t ∨
        n * caseC3Word (Subgroup.center J) u m y x t * n⁻¹ =
          caseC3Word (Subgroup.center J) u m y x (c3Mul t 40) := fun t ht => by
    rcases hnE _ (hb.caseC3Word_mem_e1EBar_iff.mpr ht) with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, hb.caseC3Word_mul])
  obtain ⟨r, hr, hra, hre⟩ : ∃ r : Fin 64, (r = 0 ∨ r = 1 ∨ r = 20 ∨ r = 21) ∧
      n * caseC3Word (Subgroup.center J) u m y x 32 * n⁻¹ =
        caseC3Word (Subgroup.center J) u m y x (c3Conj r 32) ∧
      n * caseC3Word (Subgroup.center J) u m y x 2 * n⁻¹ =
        caseC3Word (Subgroup.center J) u m y x (c3Conj r 2) := by
    rcases hnw 32 e1E_gens.1 with ha | ha <;> rcases hnw 2 e1E_gens.2.2.1 with he | he
    · exact ⟨0, by simp, by rw [ha, h0a], by rw [he, h0e]⟩
    · exact ⟨20, by simp, by rw [ha, h20a], by rw [he, h20e, h42]⟩
    · exact ⟨1, by simp, by rw [ha, h1a, h8], by rw [he, h1e]⟩
    · exact ⟨21, by simp, by rw [ha, h21a, h8], by rw [he, h21e, h42]⟩
  refine ⟨caseC3Word (Subgroup.center J) u m y x r, hb.caseC3Word_mem_e1RBar_iff.mpr (hR r hr), ?_⟩
  have hback : ∀ {a : J ⧸ Subgroup.center J} {t : Fin 64},
      n * a * n⁻¹ = caseC3Word (Subgroup.center J) u m y x (c3Conj r t) →
      (caseC3Word (Subgroup.center J) u m y x r)⁻¹ * n * a *
        ((caseC3Word (Subgroup.center J) u m y x r)⁻¹ * n)⁻¹ =
          caseC3Word (Subgroup.center J) u m y x t := fun {a t} h => by
    rw [show (caseC3Word (Subgroup.center J) u m y x r)⁻¹ * n * a *
        ((caseC3Word (Subgroup.center J) u m y x r)⁻¹ * n)⁻¹ =
        (caseC3Word (Subgroup.center J) u m y x r)⁻¹ * (n * a * n⁻¹) *
          caseC3Word (Subgroup.center J) u m y x r by group, h, ← hb.caseC3Word_conj]
    group
  have hz40 : c3Conj r 40 = 40 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
  have h := d.conj_caseC3Word_of_e1E (wa := 32) (we := 2) (by rw [hu]; exact hback hra)
    (by rw [hy]; exact hback hre) (hback (by rw [hz40]; exact hnz)) hv
  rw [e1Act_facts.2.2 v hv] at h
  nth_rewrite 1 [← h]
  group

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

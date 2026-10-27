module

public import CFSG.GH74.Uniqueness.SU.SU7Claim
public import CFSG.GH74.Uniqueness.SU.SU7Model
public import CFSG.GH74.Uniqueness.SU.SU7Gen5
public import CFSG.GH74.Uniqueness.SU.SU7Gen7

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.Blueprint

namespace L193

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

@[expose] def core (a : G) : Subgroup G :=
  (pPrimeCore 2 ↥(centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype

omit [Finite G] in
theorem core_le_cent (a : G) : core a ≤ centralizer ({a} : Set G) :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem core_conj (a : G) {g : G} (hg : g ∈ centralizer ({a} : Set G)) {w : G} (hw : w ∈ core a) :
    g * w * g⁻¹ ∈ core a := by
  obtain ⟨w', hw', rfl⟩ := hw
  exact ⟨⟨g, hg⟩ * w' * ⟨g, hg⟩⁻¹,
    (inferInstance : (pPrimeCore 2 ↥(centralizer ({a} : Set G))).Normal).conj_mem w' hw' ⟨g, hg⟩,
    rfl⟩

theorem core_odd (a : G) : Odd (Nat.card (core a)) := by
  unfold core
  rw [Subgroup.card_map_of_injective (centralizer ({a} : Set G)).subtype_injective]
  exact Nat.coprime_two_left.1
    (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(centralizer ({a} : Set G))))

theorem T_class2 (hc : Ctx19 S U M V x z A B R) {t a : G} (ht : t ∈ Tsub S U)
    (ha : a ∈ Tsub S U) : (t * a * t⁻¹) * a = a * (t * a * t⁻¹) := by
  have hemb := (Base.emb_zgen hc.hyp hc.conf hc.concl).1
  have hZc : ∀ w ∈ Zc (Tsub S U), ∀ s ∈ Tsub S U, w * s = s * w :=
    fun w hw s hs => (mem_Zc.1 hw).2 s hs
  have hcm := Gen.comm_mem_of_sq_mem hZc (Model.sq_mem_Zc hemb) t ht a ha
  have h1 := hZc _ hcm a ha
  calc (t * a * t⁻¹) * a = ((t * a * t⁻¹ * a⁻¹) * a) * a := by group
    _ = (a * (t * a * t⁻¹ * a⁻¹)) * a := by rw [h1]
    _ = a * (t * a * t⁻¹) := by group

theorem core_le_M (hc : Ctx19 S U M V x z A B R) {F : Subgroup G} (hFE : IsE 4 F)
    (hFT : F ≤ Tsub S U) {a : G} (haF : a ∈ F) : core a ≤ M := by
  classical
  have hFcomm : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f := (isElemAbelian_iff.1 hFE.1).1
  have hFa : F ≤ centralizer ({a} : Set G) := fun f hf => mem_centralizer_iff.2 (fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hFcomm a haF f hf)
  have hFW : F ≤ normalizer (core a : Set G) := fun f hf =>
    Gen.mem_normalizer_of_conj_le (fun w hw => core_conj a (hFa hf) hw)
  have hFnt : Nontrivial ↥F := by
    have : 1 < Nat.card F := by rw [hFE.2]; norm_num
    exact Finite.one_lt_card_iff_nontrivial.1 this
  apply Gen.le_of_forall_hyperplane hFE.1 hFnt hFW (core_odd a)
  intro E hEF hEi y hy
  obtain ⟨hyW, hyC⟩ := hy
  have hEcard : Nat.card E = 8 := by
    have h1 := Subgroup.card_mul_index (E.subgroupOf F)
    rw [hEi, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEF).toEquiv, hFE.2] at h1
    omega
  have hE : IsE 3 E := ⟨SU1.IsElemAbelian.mono hEF hFE.1, by rw [hEcard]; norm_num⟩
  have hN : normalizer (E : Set G) ≤ M := Claim.normalizer_le_M_of_isE hc.hyp (E := E) (F := F)
    (n := 3) (m := 4) (fun e he => Base.T_le_S (hFT (hEF he))) hE (by norm_num)
    (fun f hf => Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 (fun e he => hFcomm e (hEF he) f hf),
      Base.T_le_S (hFT hf)⟩) hFE (by norm_num)
  exact hN (Subgroup.centralizer_le_normalizer (E : Set G) hyC)

theorem core_le_O (hKI3 : K.KI3) (hc : Ctx19 S U M V x z A B R) {F : Subgroup G}
    (hFE : IsE 4 F) (hFT : F ≤ Tsub S U) {a : G} (haF : a ∈ F) (ha2 : orderOf a = 2) :
    core a ≤ (pPrimeCore 2 ↥M).map M.subtype := by
  classical
  have hH := hc.hyp
  have hconf := hc.conf
  have hcl := hc.concl
  have hWM : core a ≤ M := core_le_M hc hFE hFT haF
  have haT : a ∈ Tsub S U := hFT haF
  have haM : a ∈ M := (Base.T_le_S.trans hconf.S_le) haT
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rw [ha2, pow_two] at this
    exact this
  have ha1 : a ≠ 1 := by
    rintro rfl
    simp at ha2
  obtain ⟨ab, hab⟩ : ∃ ab : Mbar M, ab = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨a, haM⟩ :=
    ⟨_, rfl⟩
  have hab2 : orderOf ab = 2 := by
    rw [hab]; exact Claim.orderOf_proj_eq_two M haM haa ha1
  have habT : ab ∈ barImage M (Tsub S U) := by
    rw [hab]; exact Claim.mem_barImage_iff.2 ⟨⟨a, haM⟩, haT, rfl⟩
  set Qb : Subgroup (Mbar M) := barImage M (core a) with hQb
  have hQodd : Odd (Nat.card Qb) := by
    refine Odd.of_dvd_nat (core_odd a) ?_
    have h1 := Subgroup.card_map_dvd ((core a).subgroupOf M)
      (QuotientGroup.mk' (pPrimeCore 2 ↥M))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv] at h1
  have hQa : ∀ q ∈ Qb, q * ab = ab * q := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Claim.mem_barImage_iff.1 hq
    have hwC := core_le_cent a hw
    rw [hab, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 hwC a (Set.mem_singleton a)).symm
  have hQn : ∀ y : Mbar M, y * ab = ab * y → ∀ q ∈ Qb, y * q * y⁻¹ ∈ Qb := by
    intro y hy q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨w, hw, rfl⟩ := Claim.mem_barImage_iff.1 hq
    have hy' : QuotientGroup.mk' (pPrimeCore 2 ↥M) g * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨a, haM⟩ =
        QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨a, haM⟩ * QuotientGroup.mk' (pPrimeCore 2 ↥M) g := by
      rw [← hab]; exact hy
    obtain ⟨g', hg'a, hg'π⟩ := Gen.exists_cent_lift (O := pPrimeCore 2 ↥M) (Bar.odd_pPrimeCore M)
      (a := (⟨a, haM⟩ : ↥M)) (Subtype.ext haa) hy'
    have hg'C : (g' : G) ∈ centralizer ({a} : Set G) := mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]; exact (congrArg Subtype.val hg'a).symm)
    have hmemW : ((g' * w * g'⁻¹ : ↥M) : G) ∈ core a := core_conj a hg'C hw
    have e : (QuotientGroup.mk g : Mbar M) = QuotientGroup.mk' (pPrimeCore 2 ↥M) g' := hg'π.symm
    show (QuotientGroup.mk g : Mbar M) * QuotientGroup.mk' (pPrimeCore 2 ↥M) w *
      (QuotientGroup.mk g : Mbar M)⁻¹ ∈ Qb
    rw [e, ← map_inv, ← map_mul, ← map_mul]
    exact Claim.mem_barImage_iff.2 ⟨g' * w * g'⁻¹, hmemW, rfl⟩
  have hQbot : Qb = ⊥ := by
    rcases hcl.case with ha' | hb'
    · obtain ⟨hLie, -, -⟩ := ha'
      have hGH : SU0.GHGroup (Mbar M) :=
        SU0.GHGroup.of_kgh_quotient hH.kgh hH.maximal.1 (pPrimeCore 2 ↥M)
      have hO : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot ↥M
      obtain ⟨-, hcore, -⟩ := hKI3 (Mbar M) hGH hO hLie ab (hcl.T_le habT) hab2
      have hQc : Qb ≤ centralizer ({ab} : Set (Mbar M)) := fun q hq =>
        mem_centralizer_iff.2 (fun h hh => by
          rw [Set.mem_singleton_iff] at hh; rw [hh]; exact (hQa q hq).symm)
      have hnorm : (Qb.subgroupOf (centralizer ({ab} : Set (Mbar M)))).Normal :=
        ⟨fun n hn g => by
          have hn' : (n : Mbar M) ∈ Qb := hn
          have hgab : (g : Mbar M) * ab = ab * g :=
            (mem_centralizer_iff.1 g.2 ab (Set.mem_singleton ab)).symm
          exact hQn g hgab n hn'⟩
      have hcop : Nat.Coprime 2
          (Nat.card (Qb.subgroupOf (centralizer ({ab} : Set (Mbar M))))) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQc).toEquiv]
        exact Nat.coprime_two_left.2 hQodd
      have h1 := (CFSG.pPrimeCore_eq_bot_iff.1 hcore) _ hnorm hcop
      exact (Subgroup.subgroupOf_eq_bot.1 h1).eq_bot_of_le hQc
    · have hFn : (generalizedFitting (Mbar M)).Normal := Gen.normal_generalizedFitting _
      have hPn : ∀ y : Mbar M, ∀ t ∈ barImage M (Tsub S U),
          y * t * y⁻¹ ∈ barImage M (Tsub S U) := by
        intro y t ht
        rw [hb'] at ht ⊢
        exact hFn.conj_mem t ht y
      have hP2 : IsPGroup 2 ↥(barImage M (Tsub S U)) :=
        (Bar.isPGroup_subgroupOf (S.isPGroup'.to_le Base.T_le_S) M).map _
      have hCP : ∀ y : Mbar M, (∀ t ∈ barImage M (Tsub S U), y * t = t * y) →
          y ∈ barImage M (Tsub S U) := by
        intro y hy
        rw [hb']
        apply CFSG.centralizer_generalizedFitting_le (Mbar M)
        rw [mem_centralizer_iff]
        intro t ht
        exact (hy t (by rw [hb']; exact ht)).symm
      have hcl' : ∀ t ∈ barImage M (Tsub S U), (t * ab * t⁻¹) * ab = ab * (t * ab * t⁻¹) := by
        intro t ht
        obtain ⟨t₀, ht₀, rfl⟩ := Claim.mem_barImage_iff.1 ht
        have h1 := T_class2 hc ht₀ haT
        have h2 : t₀ * (⟨a, haM⟩ : ↥M) * t₀⁻¹ * ⟨a, haM⟩ =
            ⟨a, haM⟩ * (t₀ * ⟨a, haM⟩ * t₀⁻¹) := Subtype.ext h1
        have h3 := congrArg (QuotientGroup.mk' (pPrimeCore 2 ↥M)) h2
        rw [hab]
        simpa [map_mul, map_inv] using h3
      exact Gen.odd_normal_cent_eq_bot hPn hP2 hCP hcl' habT hQodd hQa hQn
  intro w hw
  have hwM : w ∈ M := hWM hw
  have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨w, hwM⟩ ∈ Qb :=
    Claim.mem_barImage_iff.2 ⟨⟨w, hwM⟩, hw, rfl⟩
  rw [hQbot, Subgroup.mem_bot] at hmem
  exact ⟨⟨w, hwM⟩, (QuotientGroup.eq_one_iff _).1 hmem, rfl⟩

theorem lemma193_a (hKI3 : K.KI3) (hc : Ctx19 S U M V x z A B R) :
    ∀ a ∈ Tsub S U, orderOf a = 2 →
      (pPrimeCore 2 ↥(centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype ≤
        (pPrimeCore 2 ↥M).map M.subtype := by
  intro a haT ha2
  have hA := hc.c19.isE16_A
  have hB := hc.c19.isE16_B
  rcases hc.c19.invol a haT ha2 with haA | haB
  · exact core_le_O hKI3 hc ⟨hA.1, by rw [hA.2]; norm_num⟩ hc.c19.A_le haA ha2
  · exact core_le_O hKI3 hc ⟨hB.1, by rw [hB.2]; norm_num⟩ hc.c19.B_le haB ha2

end L193

end CFSG.GH74.Uniqueness.SU.SU7

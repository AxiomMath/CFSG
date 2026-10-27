module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Lift
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129b
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

@[expose] noncomputable def imgSub (x : G) (Kb : Subgroup (CentralizerBar x)) [Kb.Normal] (S : Subgroup G)
    (hS : S ≤ Cx x) : Subgroup (MulAut ↥Kb) :=
  ((phiC x Kb).comp (Subgroup.inclusion hS)).range

omit [Finite G] in
theorem mem_imgSub {S : Subgroup G} (hS : S ≤ Cx x) {a : MulAut ↥Kb} :
    a ∈ imgSub x Kb S hS ↔ ∃ g ∈ S, phig x Kb g = a := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, g.2, phig_of_mem x Kb (hS g.2)⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, (phig_of_mem x Kb (hS hg)).symm⟩

omit [Finite G] in
theorem imgSub_mono {S S' : Subgroup G} (hS : S ≤ Cx x) (hS' : S' ≤ Cx x) (h : S ≤ S') :
    imgSub x Kb S hS ≤ imgSub x Kb S' hS' := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := (mem_imgSub hS).1 ha
  exact (mem_imgSub hS').2 ⟨g, h hg, rfl⟩

omit [Finite G] in
theorem isEA_imgSub {S : Subgroup G} (hS : S ≤ Cx x) (hEA : IsElemAb2 S) :
    Dihedral.IsEA (imgSub x Kb S hS) := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := (mem_imgSub hS).1 ha
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← phig_mul x Kb (hS hg) (hS hg), (hEA g hg).1, phig_one]
  · obtain ⟨g', hg', rfl⟩ := (mem_imgSub hS).1 hb
    rw [← phig_mul x Kb (hS hg) (hS hg'), ← phig_mul x Kb (hS hg') (hS hg), (hEA g hg).2 g' hg']

omit [Finite G] in
theorem Rd_le_C (_h : SitFacts x Kb e N T) : Rdg x Kb e T ≤ Cx x := fun _ hg => hg.2.1

omit [Finite G] in
theorem NP_le_imgRd (h : SitFacts x Kb e N T) : N.P ≤ imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := (h.hPN a).1 ha
  exact (mem_imgSub (Rd_le_C h)).2 ⟨p, SitFacts.Pg_le_Rd hp, rfl⟩

omit [Finite G] in
theorem imgRd_le_NPt (h : SitFacts x Kb e N T) : imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) ≤ N.Pt := by
  intro a ha
  obtain ⟨r, hr, rfl⟩ := (mem_imgSub (Rd_le_C h)).1 ha
  exact ⟨h.hTN r hr.1, hr.2.2⟩

theorem imgRd_cases (h : SitFacts x Kb e N T) :
    imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) = N.P ∨
      imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) = N.Pt := by
  by_cases hP : imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) = N.P
  · exact Or.inl hP
  · right
    apply le_antisymm (imgRd_le_NPt h)
    have hidx := NPt_index_two (e := e) (N := N) h.hF
    obtain ⟨a₀, ha₀, ha₀P⟩ : ∃ a ∈ imgSub x Kb (Rdg x Kb e T) (Rd_le_C h), a ∉ N.P := by
      by_contra hcon
      push Not at hcon
      exact hP (le_antisymm hcon (NP_le_imgRd h))
    intro b hb
    by_cases hbP : b ∈ N.P
    · exact NP_le_imgRd h hbP
    · have hmul := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨b⁻¹, N.Pt.inv_mem hb⟩ : ↥N.Pt))
        (b := ⟨a₀, imgRd_le_NPt h ha₀⟩)).2 (by
          constructor
          · intro h1; exact absurd (inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 h1)) hbP
          · intro h2; exact absurd (Subgroup.mem_subgroupOf.1 h2) ha₀P)
      have hbq : b⁻¹ * a₀ ∈ N.P := Subgroup.mem_subgroupOf.1 hmul
      have : b = a₀ * (b⁻¹ * a₀)⁻¹ := by group
      rw [this]
      exact mul_mem ha₀ (inv_mem (NP_le_imgRd h hbq))

theorem imgRd_dihedral (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) (h12d : IVK.IVK_1_2d) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(imgSub x Kb (Rdg x Kb e T) (Rd_le_C h)) ≃*
      DihedralGroup (2 ^ m)) := by
  rcases imgRd_cases h with hc | hc
  · obtain ⟨m, hm, ⟨e₀⟩⟩ := NP_dihedral (e := e) (N := N) h.hF h12c
    exact ⟨m, hm, ⟨(MulEquiv.subgroupCongr hc).trans e₀⟩⟩
  · obtain ⟨-, -, -, n₁, hn₁⟩ := h12d F h.hF ↥Kb e N
    obtain ⟨m, hm, -, ⟨e₁⟩⟩ := isDihedralTwoGroup_equiv hn₁
    exact ⟨m, hm, ⟨(MulEquiv.subgroupCongr hc).trans e₁⟩⟩

theorem ip_Rd_dihedral (h : SitFacts x Kb e N T) (hQ : Qg x Kb T = Subgroup.zpowers x)
    (h12c : IVK.IVK_1_2c) (h12d : IVK.IVK_1_2d) : IP_Rd_dihedral x (Rdg x Kb e T) := by
  intro P' hP'Rd hP'x hP'sup
  have hP'C : P' ≤ Cx x := fun g hg => (hP'Rd hg).2.1
  let Φ : ↥P' →* MulAut ↥Kb := (phiC x Kb).comp (Subgroup.inclusion hP'C)
  have hΦ : ∀ g : ↥P', Φ g = phig x Kb g := fun g => (phig_of_mem x Kb (hP'C g.2)).symm
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : phig x Kb g = 1 := by rw [← hΦ]; exact hg
    have h2 : (g : G) ∈ Qg x Kb T := ⟨(hP'Rd g.2).1, hP'C g.2, h1⟩
    rw [hQ] at h2
    have h3 : (g : G) ∈ P' ⊓ Subgroup.zpowers x := ⟨g.2, h2⟩
    rw [hP'x, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hrange : Φ.range = imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) := by
    ext a
    rw [mem_imgSub (Rd_le_C h)]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, hP'Rd g.2, (hΦ g).symm⟩
    · rintro ⟨r, hr, rfl⟩
      have hr' : r ∈ P' ⊔ Subgroup.zpowers x := by rw [hP'sup]; exact hr
      have hcomm : ∀ a ∈ P', ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
        intro a ha b hb
        have hxa : a * x = x * a := (mem_Cx x).1 (hP'C ha)
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact ((commute_of_mul_eq hxa).zpow_right k).eq
      obtain ⟨p, hp, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm).1 hr'
      have hbQ : b ∈ Qg x Kb T := by rw [hQ]; exact hb
      refine ⟨⟨p, hp⟩, ?_⟩
      rw [hΦ]
      show phig x Kb p = phig x Kb (p * b)
      rw [phig_mul x Kb (hP'C hp) hbQ.2.1, hbQ.2.2, mul_one]
  obtain ⟨m, hm, ⟨e₂⟩⟩ := imgRd_dihedral h h12c h12d
  have e₃ : ↥P' ≃* DihedralGroup (2 ^ m) :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans e₂
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  exact Dihedral.isDihedral2_of_equiv e₃

omit [Finite G] in
theorem zpowers_sq_one {x : G} (hx : x * x = 1) : ∀ b ∈ Subgroup.zpowers x, b * b = 1 := by
  intro b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hx, one_zpow]

omit [Finite G] in
theorem zpowers_comm (x : G) : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [← zpow_add, ← zpow_add, add_comm]

theorem elemAb8_data (h : SitFacts x Kb e N T) (hQ : Qg x Kb T = Subgroup.zpowers x)
    (hrk : Rank2Le (Cx x) 3) (hx : x * x = 1) (hx1 : x ≠ 1) {E : Subgroup G} (hET : E ≤ T)
    (hE : IsElemAb2 E) (hc : Nat.card E = 8) :
    x ∈ E ∧ (∀ t ∈ T, t ∈ E ↔ phig x Kb t ∈ imgSub x Kb E (hET.trans h.T_le_C)) ∧
      Dihedral.IsEA (imgSub x Kb E (hET.trans h.T_le_C)) ∧
      Nat.card (imgSub x Kb E (hET.trans h.T_le_C)) = 4 := by
  have hEC : E ≤ Cx x := hET.trans h.T_le_C
  have hxT : x ∈ T := x_mem_of_sylow x h.sylow hx hx1
  have hxC : x ∈ Cx x := x_mem_Cx x
  have hxE : x ∈ E := by
    have hcomm : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
      intro a ha b hb
      have hxa : a * x = x * a := (mem_Cx x).1 (hEC ha)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((commute_of_mul_eq hxa).zpow_right k).eq
    have hE₁C : E ⊔ Subgroup.zpowers x ≤ Cx x := sup_le hEC (Subgroup.zpowers_le.2 hxC)
    have hE₁ : IsElemAb2 (E ⊔ Subgroup.zpowers x) := by
      intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm).1 hg
      have hbb := zpowers_sq_one hx b hb
      have haa := (hE a ha).1
      have hab := hcomm a ha b hb
      refine ⟨?_, ?_⟩
      · calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
          _ = a * (a * b) * b := by rw [← hab]
          _ = (a * a) * (b * b) := by simp only [mul_assoc]
          _ = 1 := by rw [haa, hbb, mul_one]
      · intro g' hg'
        obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_of_comm hcomm).1 hg'
        have h1 : a * a' = a' * a := (hE a ha).2 a' ha'
        have h2 : b * b' = b' * b := zpowers_comm x b hb b' hb'
        have h3 : a * b' = b' * a := hcomm a ha b' hb'
        have h4 : a' * b = b * a' := hcomm a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
          _ = a * (a' * b) * b' := by rw [h4]
          _ = (a * a') * (b * b') := by simp only [mul_assoc]
          _ = (a' * a) * (b' * b) := by rw [h1, h2]
          _ = a' * (a * b') * b := by simp only [mul_assoc]
          _ = a' * (b' * a) * b := by rw [h3]
          _ = a' * b' * (a * b) := by simp only [mul_assoc]
    have hcard := hrk _ hE₁C hE₁
    have heq : E = E ⊔ Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc]; simpa using hcard)
    rw [heq]
    exact mem_sup_right (Subgroup.mem_zpowers x)
  have hchar : ∀ t ∈ T, t ∈ E ↔ phig x Kb t ∈ imgSub x Kb E hEC := by
    intro t ht
    constructor
    · intro htE; exact (mem_imgSub hEC).2 ⟨t, htE, rfl⟩
    · intro ha
      obtain ⟨g, hg, hgt⟩ := (mem_imgSub hEC).1 ha
      have hgC := hEC hg
      have htC := h.T_le_C ht
      have hq : g⁻¹ * t ∈ Qg x Kb T := ⟨T.mul_mem (T.inv_mem (hET hg)) ht, mul_mem (inv_mem hgC) htC, by
        rw [phig_mul x Kb (inv_mem hgC) htC, phig_inv x Kb hgC, hgt, inv_mul_cancel]⟩
      rw [hQ] at hq
      have hqE : g⁻¹ * t ∈ E := Subgroup.zpowers_le.2 hxE hq
      have : t = g * (g⁻¹ * t) := by group
      rw [this]
      exact E.mul_mem hg hqE
  refine ⟨hxE, hchar, isEA_imgSub hEC hE, ?_⟩
  let Φ : ↥E →* MulAut ↥Kb := (phiC x Kb).comp (Subgroup.inclusion hEC)
  have hΦ : ∀ g : ↥E, Φ g = phig x Kb g := fun g => (phig_of_mem x Kb (hEC g.2)).symm
  have hker : Φ.ker = (Subgroup.zpowers x).subgroupOf E := by
    ext g
    rw [MonoidHom.mem_ker, hΦ, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have : (g : G) ∈ Qg x Kb T := ⟨hET g.2, hEC g.2, h1⟩
      rwa [hQ] at this
    · intro h1
      have : (g : G) ∈ Qg x Kb T := by rw [hQ]; exact h1
      exact this.2.2
  have hxorder : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hkercard : Nat.card Φ.ker = 2 := by
    rw [hker, card_subgroupOf (Subgroup.zpowers_le.2 hxE), Nat.card_zpowers, hxorder]
  have h1 := Subgroup.card_mul_index Φ.ker
  rw [Subgroup.index_ker, hkercard, hc] at h1
  show Nat.card Φ.range = 4
  omega

theorem ip_Rd_fuse (h : SitFacts x Kb e N T) (hQ : Qg x Kb T = Subgroup.zpowers x)
    (hrk : Rank2Le (Cx x) 3) (hx : x * x = 1) (hx1 : x ≠ 1) (_h12c : IVK.IVK_1_2c)
    (_h12d : IVK.IVK_1_2d) (h13fa : IVK.IVK_1_3f_a) : IP_Rd_fuse x (Pg x Kb T) (Rdg x Kb e T) := by
  intro hne E E' hEPx hE'Px hE hE' hc hc'
  have hxT : x ∈ T := x_mem_of_sylow x h.sylow hx hx1
  have hPxT : Pg x Kb T ⊔ Subgroup.zpowers x ≤ T := sup_le inf_le_left (Subgroup.zpowers_le.2 hxT)
  have hET : E ≤ T := hEPx.trans hPxT
  have hE'T : E' ≤ T := hE'Px.trans hPxT
  have hEC : E ≤ Cx x := hET.trans h.T_le_C
  have hE'C : E' ≤ Cx x := hE'T.trans h.T_le_C
  obtain ⟨hxE, hcharE, hEA, hcardE⟩ := elemAb8_data h hQ hrk hx hx1 hET hE hc
  obtain ⟨hxE', hcharE', hEA', hcardE'⟩ := elemAb8_data h hQ hrk hx hx1 hE'T hE' hc'
  have hcommPx : ∀ a ∈ Pg x Kb T, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    have hxa : a * x = x * a := (mem_Cx x).1 (h.T_le_C ha.1)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((commute_of_mul_eq hxa).zpow_right k).eq
  have himgP : ∀ (S : Subgroup G) (hSC : S ≤ Cx x), S ≤ Pg x Kb T ⊔ Subgroup.zpowers x →
      imgSub x Kb S hSC ≤ N.P := by
    intro S hSC hS a ha
    obtain ⟨g, hg, rfl⟩ := (mem_imgSub hSC).1 ha
    obtain ⟨p, hp, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcommPx).1 (hS hg)
    have hbQ : b ∈ Qg x Kb T := by rw [hQ]; exact hb
    rw [phig_mul x Kb (h.T_le_C hp.1) hbQ.2.1, hbQ.2.2, mul_one]
    exact (h.hPN _).2 ⟨p, hp, rfl⟩
  have himg : imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) = N.Pt := by
    rcases imgRd_cases h with hc1 | hc1
    · exfalso
      apply hne
      apply le_antisymm
      · rw [← hQ]; exact SitFacts.PQ_le_Rd
      · intro r hr
        have hinn : phig x Kb r ∈ IVK.innAut ↥Kb := by
          have : phig x Kb r ∈ imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) :=
            (mem_imgSub (Rd_le_C h)).2 ⟨r, hr, rfl⟩
          rw [hc1] at this
          exact (NP_mem_iff.1 this).2
        have := h.mem_PQ_of_inn hr hinn
        rw [hQ] at this
        exact this
    · exact hc1
  have hfour : ∀ (S : Subgroup G) (hSC : S ≤ Cx x), Dihedral.IsEA (imgSub x Kb S hSC) →
      Nat.card (imgSub x Kb S hSC) = 4 → IVK.IsFourSubgroup (imgSub x Kb S hSC) :=
    fun S hSC hS hc4 => isFourSubgroup_of_isEA hS hc4
  obtain ⟨g, hgPt, hgmap⟩ := h13fa F h.hF ↥Kb e N _ _ (himgP E hEC hEPx) (himgP E' hE'C hE'Px)
    (hfour E hEC hEA hcardE) (hfour E' hE'C hEA' hcardE')
  have hginv : g⁻¹ ∈ imgSub x Kb (Rdg x Kb e T) (Rd_le_C h) := by
    rw [himg]; exact N.Pt.inv_mem hgPt
  obtain ⟨r, hr, hrg⟩ := (mem_imgSub (Rd_le_C h)).1 hginv
  refine ⟨r, hr, ?_⟩
  have hrT : r ∈ T := hr.1
  have hrC : r ∈ Cx x := hr.2.1
  have hmemE' : ∀ b, b ∈ imgSub x Kb E' hE'C ↔ ∃ ē ∈ imgSub x Kb E hEC, g * ē * g⁻¹ = b := by
    intro b
    rw [← hgmap]
    simp [Subgroup.mem_map, MulAut.conj_apply]
  have hconjphi : ∀ a ∈ T, phig x Kb (r * a * r⁻¹) = g⁻¹ * phig x Kb a * g := by
    intro a ha
    rw [phig_mul x Kb (mul_mem hrC (h.T_le_C ha)) (inv_mem hrC), phig_mul x Kb hrC (h.T_le_C ha),
      phig_inv x Kb hrC, hrg, inv_inv]
  ext a
  rw [mem_Hconj]
  constructor
  · intro ha
    have haT : a ∈ T := hE'T ha
    have h1 : phig x Kb a ∈ imgSub x Kb E' hE'C := (mem_imgSub hE'C).2 ⟨a, ha, rfl⟩
    obtain ⟨ē, hē, hēa⟩ := (hmemE' _).1 h1
    have hraT : r * a * r⁻¹ ∈ T := T.mul_mem (T.mul_mem hrT haT) (T.inv_mem hrT)
    rw [hcharE _ hraT, hconjphi a haT, ← hēa]
    have : g⁻¹ * (g * ē * g⁻¹) * g = ē := by group
    rw [this]; exact hē
  · intro hra
    have hraT : r * a * r⁻¹ ∈ T := hET hra
    have haT : a ∈ T := by
      have : a = r⁻¹ * (r * a * r⁻¹) * r := by group
      rw [this]; exact T.mul_mem (T.mul_mem (T.inv_mem hrT) hraT) hrT
    rw [hcharE _ hraT, hconjphi a haT] at hra
    rw [hcharE' _ haT, hmemE']
    exact ⟨_, hra, by group⟩

theorem ip_E8_two (h : SitFacts x Kb e N T) (hQ : Qg x Kb T = Subgroup.zpowers x)
    (hΩ : omega1 T ≤ Rdg x Kb e T) (hrk : Rank2Le (Cx x) 3) (hx : x * x = 1) (hx1 : x ≠ 1)
    (h12c : IVK.IVK_1_2c) (h12d : IVK.IVK_1_2d) : IP_E8_two T := by
  rintro ⟨E₀, hE₀T, hE₀, hc₀, hE₀n⟩ E₁ E₂ E₃ hT₁ hT₂ hT₃ h₁ h₂ h₃ c₁ c₂ c₃
  have hRd : ∀ E : Subgroup G, E ≤ T → IsElemAb2 E → E ≤ Rdg x Kb e T := fun E hET hE g hg =>
    hΩ (Subgroup.subset_closure ⟨hET hg, (hE g hg).1⟩)
  have hD := Rd_le_C h
  obtain ⟨m, hm, ⟨eD⟩⟩ := imgRd_dihedral h h12c h12d
  have hNZ : NeZero (2 ^ m) := ⟨by positivity⟩
  have hk2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have data : ∀ E : Subgroup G, ∀ hET : E ≤ T, IsElemAb2 E → Nat.card E = 8 →
      ∃ hEC : E ≤ Cx x, (∀ t ∈ T, t ∈ E ↔ phig x Kb t ∈ imgSub x Kb E hEC) ∧
        Dihedral.IsEA ((imgSub x Kb E hEC).subgroupOf (imgSub x Kb (Rdg x Kb e T) hD)) ∧
        Nat.card ((imgSub x Kb E hEC).subgroupOf (imgSub x Kb (Rdg x Kb e T) hD)) = 4 := by
    intro E hET hE hc
    obtain ⟨-, hchar, hEA, hcard⟩ := elemAb8_data h hQ hrk hx hx1 hET hE hc
    have hEC := hET.trans h.T_le_C
    have hle : imgSub x Kb E hEC ≤ imgSub x Kb (Rdg x Kb e T) hD :=
      imgSub_mono hEC hD (hRd E hET hE)
    exact ⟨hEC, hchar, isEA_subgroupOf' hEA, by rw [card_subgroupOf hle]; exact hcard⟩
  obtain ⟨hC₀, hch₀, hEA₀, hcard₀⟩ := data E₀ hE₀T hE₀ hc₀
  have hn₀ : ((imgSub x Kb E₀ hC₀).subgroupOf (imgSub x Kb (Rdg x Kb e T) hD)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : MulAut ↥Kb) ∈ imgSub x Kb E₀ hC₀ := Subgroup.mem_subgroupOf.1 hn
    obtain ⟨e₀, he₀, hne⟩ := (mem_imgSub hC₀).1 hn'
    obtain ⟨r, hr, hrg⟩ := (mem_imgSub hD).1 g.2
    refine Subgroup.mem_subgroupOf.2 ((mem_imgSub hC₀).2 ⟨r * e₀ * r⁻¹, hE₀n r hr.1 e₀ he₀, ?_⟩)
    have hrC := hr.2.1
    have he₀C := hC₀ he₀
    show phig x Kb (r * e₀ * r⁻¹) = (g : MulAut ↥Kb) * n * (g : MulAut ↥Kb)⁻¹
    rw [phig_mul x Kb (mul_mem hrC he₀C) (inv_mem hrC), phig_mul x Kb hrC he₀C, phig_inv x Kb hrC,
      hrg, hne]
  have hk4 : 2 ^ m ≤ 4 := Dihedral.le_four_of_normal_four_of_equiv eD hk2 hEA₀ hcard₀ hn₀
  have hk : 2 ^ m = 2 ∨ 2 ^ m = 4 := by
    have hm2 : m ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl <;> simp
  obtain ⟨hC₁, hch₁, hEA₁, hcard₁⟩ := data E₁ hT₁ h₁ c₁
  obtain ⟨hC₂, hch₂, hEA₂, hcard₂⟩ := data E₂ hT₂ h₂ c₂
  obtain ⟨hC₃, hch₃, hEA₃, hcard₃⟩ := data E₃ hT₃ h₃ c₃
  have key : ∀ (E E' : Subgroup G) (hEC : E ≤ Cx x) (hE'C : E' ≤ Cx x), E ≤ T → E' ≤ T →
      E ≤ Rdg x Kb e T → E' ≤ Rdg x Kb e T →
      (∀ t ∈ T, t ∈ E ↔ phig x Kb t ∈ imgSub x Kb E hEC) →
      (∀ t ∈ T, t ∈ E' ↔ phig x Kb t ∈ imgSub x Kb E' hE'C) →
      ((imgSub x Kb E hEC).subgroupOf (imgSub x Kb (Rdg x Kb e T) hD) =
        (imgSub x Kb E' hE'C).subgroupOf (imgSub x Kb (Rdg x Kb e T) hD)) → E = E' := by
    intro E E' hEC hE'C hET hE'T hERd hE'Rd hchE hchE' heq
    have h1 := Subgroup.subgroupOf_inj.1 heq
    rw [inf_eq_left.2 (imgSub_mono hEC hD hERd), inf_eq_left.2 (imgSub_mono hE'C hD hE'Rd)] at h1
    ext t
    constructor
    · intro ht
      rw [hchE' t (hET ht), ← h1]
      exact (mem_imgSub hEC).2 ⟨t, ht, rfl⟩
    · intro ht
      rw [hchE t (hE'T ht), h1]
      exact (mem_imgSub hE'C).2 ⟨t, ht, rfl⟩
  rcases Dihedral.four_subgroups_pigeon_of_equiv eD hk hEA₁ hcard₁ hEA₂ hcard₂ hEA₃ hcard₃ with
    h12 | h13 | h23
  · exact Or.inl (key E₁ E₂ hC₁ hC₂ hT₁ hT₂ (hRd E₁ hT₁ h₁) (hRd E₂ hT₂ h₂) hch₁ hch₂ h12)
  · exact Or.inr (Or.inl (key E₁ E₃ hC₁ hC₃ hT₁ hT₃ (hRd E₁ hT₁ h₁) (hRd E₃ hT₃ h₃) hch₁ hch₃ h13))
  · exact Or.inr (Or.inr (key E₂ E₃ hC₂ hC₃ hT₂ hT₃ (hRd E₂ hT₂ h₂) (hRd E₃ hT₃ h₃) hch₂ hch₃ h23))

end CFSG.GH74.GLS.Stage1.Thm6.Glue

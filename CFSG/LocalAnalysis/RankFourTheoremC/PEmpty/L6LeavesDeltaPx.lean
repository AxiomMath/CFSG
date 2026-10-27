module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Frattini
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaCyc
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6Delta

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {A : Type} [Group A] [Finite A]

@[expose] def Pxc (P : Subgroup A) (x : A) : Subgroup A := P ⊓ centralizer ({x} : Set A)

theorem mem_Pxc {P : Subgroup A} {x y : A} :
    y ∈ Pxc P x ↔ y ∈ P ∧ y ∈ centralizer ({x} : Set A) := Iff.rfl

theorem exists_elemAbelian_cube_of_four_le {p : ℕ} [hp : Fact p.Prime] (P : Sylow p A)
    (h4 : 4 ≤ Open.pRank p (P : Subgroup A)) :
    ∃ T : Subgroup A, T ≤ (P : Subgroup A) ∧ CFSG.Open.IsElemAbelian p T ∧
      Nat.card T = p ^ 3 := by
  obtain ⟨E, hEP, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (P : Subgroup A)
  have hdvd : p ^ 3 ∣ Nat.card E := by
    rw [hEc]
    exact pow_dvd_pow p (by omega)
  obtain ⟨T, hTc, -, hTE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp.out (H := ⊥) (L := E) (by simp) hdvd bot_le
  exact ⟨T, hTE.trans hEP, CFSG.Open.IsElemAbelian.mono hE hTE, hTc⟩

theorem plane_le_Pxc {p : ℕ} {P : Sylow p A} {X : Subgroup A} {x z : A}
    (h : Plane65 p P X x z) : zpowers x ⊔ zpowers z ≤ Pxc (P : Subgroup A) x := by
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup A) := h.plane.isIsolatedPlane.1
  have hxP : x ∈ (P : Subgroup A) := hBP (mem_sup_left (mem_zpowers x))
  have hzP : z ∈ (P : Subgroup A) := hBP (mem_sup_right (mem_zpowers z))
  refine sup_le (zpowers_le.mpr (mem_Pxc.mpr ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩)) ?_
  refine zpowers_le.mpr (mem_Pxc.mpr ⟨hzP, mem_centralizer_singleton_iff.mpr ?_⟩)
  exact (mem_centralizer_iff.mp h.z_central x hxP).symm

theorem mem_plane_of_mem_Pxc {p : ℕ} {P : Sylow p A} {X : Subgroup A} {x z : A}
    (h : Plane65 p P X x z) {y : A} (hy : y ∈ Pxc (P : Subgroup A) x) (hyp : y ^ p = 1) :
    y ∈ zpowers x ⊔ zpowers z := by
  obtain ⟨hyP, hyC⟩ := mem_Pxc.mp hy
  refine h.plane.mem_of_mem_centralizer y ?_ hyp
  have hyx : y * x = x * y := mem_centralizer_singleton_iff.mp hyC
  have hyz : y * z = z * y := mem_centralizer_iff.mp h.z_central y hyP
  have hle : zpowers x ⊔ zpowers z ≤ centralizer ({y} : Set A) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyx.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyz.symm))
  rw [mem_centralizer_iff]
  intro g hg
  exact mem_centralizer_singleton_iff.mp (hle (SetLike.mem_coe.mp hg))

theorem x_not_mem_frattini_Pxc {p : ℕ} {P : Sylow p A} {X : Subgroup A} {x z : A}
    (h : Plane65 p P X x z) :
    x ∉ (frattini ↥(Pxc (P : Subgroup A) x)).map (Pxc (P : Subgroup A) x).subtype := by
  classical
  have hprime := h.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hxB : x ∈ zpowers x ⊔ zpowers z := mem_sup_left (mem_zpowers x)
  have hxPx : x ∈ Pxc (P : Subgroup A) x := plane_le_Pxc h hxB
  have hxP : x ∈ (P : Subgroup A) := (mem_Pxc.mp hxPx).1
  have hPxP : Pxc (P : Subgroup A) x ≤ (P : Subgroup A) := fun y hy => (mem_Pxc.mp hy).1
  rintro ⟨g, hg, hgx⟩
  have hgfr : (subgroupOfEquivOfLe hPxP).symm g ∈
      frattini ↥((Pxc (P : Subgroup A) x).subgroupOf (P : Subgroup A)) :=
    Subgroup.mem_comap.mp (frattini_le_comap_frattini_of_surjective
      (φ := (subgroupOfEquivOfLe hPxP).symm.toMonoidHom)
      (subgroupOfEquivOfLe hPxP).symm.surjective hg)
  have hxmem : (⟨x, hxP⟩ : (P : Subgroup A)) ∈
      (Pxc (P : Subgroup A) x).subgroupOf (P : Subgroup A) :=
    mem_subgroupOf.mpr hxPx
  have heq : (subgroupOfEquivOfLe hPxP).symm g = ⟨⟨x, hxP⟩, hxmem⟩ :=
    Subtype.ext (Subtype.ext hgx)
  have hgfr' : (⟨⟨x, hxP⟩, hxmem⟩ :
      ↥((Pxc (P : Subgroup A) x).subgroupOf (P : Subgroup A))) ∈
      frattini ↥((Pxc (P : Subgroup A) x).subgroupOf (P : Subgroup A)) := by
    rw [← heq]
    exact hgfr
  have hxp : (⟨x, hxP⟩ : (P : Subgroup A)) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h.plane.isElemAbelian.2 x hxB
  obtain ⟨T, hTP, hTe, hTc⟩ := exists_elemAbelian_cube_of_four_le P h.four_le
  haveI hTel : CFSG.IsElementaryAbelian p ↥T :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p T).2 hTe
  haveI hTPel : CFSG.IsElementaryAbelian p ↥(T.subgroupOf (P : Subgroup A)) :=
    CFSG.IsElementaryAbelian.subgroupOf hTP
  have hTc' : Nat.card ↥(T.subgroupOf (P : Subgroup A)) = p ^ 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTP).toEquiv]
    exact hTc
  obtain ⟨E, hEC, hEe, hE3⟩ := exists_centralizer_rank_three_of_mem_frattini
    (by have := h.five_le; omega) P.isPGroup' hxp ⟨hxmem, hgfr'⟩ hTPel hTc'
  have hEA : E.map (P : Subgroup A).subtype ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨e, he, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hEC he)))
  haveI : CFSG.IsElementaryAbelian p ↥E := hEe
  have hEel : CFSG.Open.IsElemAbelian p (E.map (P : Subgroup A).subtype) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      CFSG.IsElementaryAbelian.map_subtype
  have hEp : IsPGroup p ↥E := P.isPGroup'.to_subgroup E
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hcardmap : Nat.card ↥(E.map (P : Subgroup A).subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective (P : Subgroup A).subtype_injective]
    exact hk
  have hk3 : 3 ≤ k := by
    rw [hk] at hE3
    exact (Nat.pow_le_pow_iff_right hprime.one_lt).mp hE3
  have hrank := CFSG.SectionRank.le_pRank hprime.one_lt hEA hEel hcardmap
  have h2 := h.rank_centralizer
  omega

theorem comm_Pxc_sub {p : ℕ} {P : Sylow p A} {X : Subgroup A} {x z : A}
    (h : Plane65 p P X x z) (a b : ↥(Pxc (P : Subgroup A) x)) : a * b = b * a := by
  classical
  have hprime := h.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hxB : x ∈ zpowers x ⊔ zpowers z := mem_sup_left (mem_zpowers x)
  have hxPx : x ∈ Pxc (P : Subgroup A) x := plane_le_Pxc h hxB
  have hxcent : ∀ g : ↥(Pxc (P : Subgroup A) x), g * ⟨x, hxPx⟩ = ⟨x, hxPx⟩ * g := by
    intro g
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (mem_Pxc.mp g.2).2
  have hx'fr : (⟨x, hxPx⟩ : ↥(Pxc (P : Subgroup A) x)) ∉
      frattini ↥(Pxc (P : Subgroup A) x) := fun hmem =>
    x_not_mem_frattini_Pxc h ⟨_, hmem, rfl⟩
  obtain ⟨D, hDc, hxD⟩ := exists_coatom_not_mem_of_not_mem_frattini hx'fr
  have hDtop : D ⊔ zpowers (⟨x, hxPx⟩ : ↥(Pxc (P : Subgroup A) x)) = ⊤ := by
    apply hDc.2
    refine lt_of_le_of_ne le_sup_left (fun heq => hxD ?_)
    have hle : zpowers (⟨x, hxPx⟩ : ↥(Pxc (P : Subgroup A) x)) ≤ D := by
      rw [heq]
      exact le_sup_right
    exact hle (mem_zpowers _)
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, bot_sup_eq] at hDtop
    have hzPx : z ∈ Pxc (P : Subgroup A) x := plane_le_Pxc h (mem_sup_right (mem_zpowers z))
    have hz' : (⟨z, hzPx⟩ : ↥(Pxc (P : Subgroup A) x)) ∈
        zpowers (⟨x, hxPx⟩ : ↥(Pxc (P : Subgroup A) x)) := by
      rw [hDtop]
      exact mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
    have hzx : z ∈ zpowers x :=
      Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hBeq : zpowers x ⊔ zpowers z = zpowers x := sup_eq_left.mpr (zpowers_le.mpr hzx)
    have hcard := h.plane.card_eq
    rw [hBeq, Nat.card_zpowers] at hcard
    have hxp : x ^ p = 1 := h.plane.isElemAbelian.2 x hxB
    have hord : orderOf x ≤ p := Nat.le_of_dvd h.prime.pos (orderOf_dvd_of_pow_eq_one hxp)
    have h2 : p ^ 2 ≤ p := by
      rw [← hcard]
      exact hord
    have h5 := h.five_le
    nlinarith
  have hPxp : IsPGroup p ↥(Pxc (P : Subgroup A) x) := by
    intro g
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g.1, (mem_Pxc.mp g.2).1⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  have hDp : IsPGroup p ↥D := hPxp.to_subgroup D
  set Bx : Subgroup ↥(Pxc (P : Subgroup A) x) :=
    (zpowers x ⊔ zpowers z).subgroupOf (Pxc (P : Subgroup A) x) with hBxdef
  have hΩ : ∀ g ∈ D, g ^ p = 1 → g ∈ Bx := by
    intro g _ hgp
    refine mem_subgroupOf.mpr (mem_plane_of_mem_Pxc h g.2 ?_)
    simpa using congrArg Subtype.val hgp
  have hBx : Nat.card ↥Bx = p ^ 2 := by
    rw [hBxdef, Nat.card_congr (subgroupOfEquivOfLe (plane_le_Pxc h)).toEquiv]
    exact h.plane.card_eq
  have hxBx : (⟨x, hxPx⟩ : ↥(Pxc (P : Subgroup A) x)) ∈ Bx := mem_subgroupOf.mpr hxB
  have hWcard : Nat.card ↥(Bx ⊓ D) = p :=
    card_inf_eq_prime Bx D hBx hDp hDne hΩ ⟨_, hxBx, hxD⟩
  have hU₀card : Nat.card ↥((Bx ⊓ D).subgroupOf D) = p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : Bx ⊓ D ≤ D)).toEquiv]
    exact hWcard
  have hcyc : IsCyclic ↥D := by
    refine isCyclic_of_pow_eq_one_mem ?_ hDp ((Bx ⊓ D).subgroupOf D) hU₀card ?_
    · have := h.five_le
      omega
    · intro g hg
      refine mem_subgroupOf.mpr ⟨?_, g.2⟩
      exact hΩ g.1 g.2 (by simpa using congrArg Subtype.val hg)
  haveI := hcyc
  have hDcomm : ∀ c d : ↥(Pxc (P : Subgroup A) x), c ∈ D → d ∈ D → c * d = d * c := by
    intro c d hc hd
    exact congrArg Subtype.val (comm_of_isCyclic (G := ↥D) ⟨c, hc⟩ ⟨d, hd⟩)
  have hcentD : ∀ c : ↥(Pxc (P : Subgroup A) x), ∀ d ∈ D, c * d = d * c := by
    intro c
    have htop : (⊤ : Subgroup ↥(Pxc (P : Subgroup A) x)) ≤
        Subgroup.centralizer (D : Set ↥(Pxc (P : Subgroup A) x)) := by
      rw [← hDtop]
      refine sup_le (fun d hd => ?_) ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro e he
        exact hDcomm e d he hd
      · rw [zpowers_le, Subgroup.mem_centralizer_iff]
        intro e _
        exact hxcent e
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp (htop (mem_top c)) d hd).symm
  have hsup : D ⊔ zpowers (⟨x, hxPx⟩ : ↥(Pxc (P : Subgroup A) x)) ≤
      centralizer ({a} : Set ↥(Pxc (P : Subgroup A) x)) := by
    refine sup_le (fun d hd => ?_) ?_
    · rw [mem_centralizer_singleton_iff]
      exact (hcentD a d hd).symm
    · rw [zpowers_le, mem_centralizer_singleton_iff]
      exact (hxcent a).symm
  rw [hDtop] at hsup
  exact (mem_centralizer_singleton_iff.mp (hsup (mem_top b))).symm

theorem comm_Pxc {p : ℕ} {P : Sylow p A} {X : Subgroup A} {x z : A} (h : Plane65 p P X x z)
    {a b : A} (ha : a ∈ Pxc (P : Subgroup A) x) (hb : b ∈ Pxc (P : Subgroup A) x) :
    a * b = b * a :=
  congrArg Subtype.val (comm_Pxc_sub h ⟨a, ha⟩ ⟨b, hb⟩)

theorem mem_normalizer_plane {p : ℕ} {P : Sylow p A} {X : Subgroup A} {x z : A}
    (h : Plane65 p P X x z) {g : A}
    (hfw : ∀ y ∈ Pxc (P : Subgroup A) x, g * y * g⁻¹ ∈ Pxc (P : Subgroup A) x)
    (hbw : ∀ y ∈ Pxc (P : Subgroup A) x, g⁻¹ * y * g⁻¹⁻¹ ∈ Pxc (P : Subgroup A) x) :
    g ∈ Subgroup.normalizer ((zpowers x ⊔ zpowers z : Subgroup A) : Set A) := by
  have fwd : ∀ m : A, (∀ y ∈ Pxc (P : Subgroup A) x, m * y * m⁻¹ ∈ Pxc (P : Subgroup A) x) →
      ∀ b ∈ zpowers x ⊔ zpowers z, m * b * m⁻¹ ∈ zpowers x ⊔ zpowers z := by
    intro m hm b hb
    refine mem_plane_of_mem_Pxc h (hm b (plane_le_Pxc h hb)) ?_
    rw [conj_pow, h.plane.isElemAbelian.2 b hb, mul_one, mul_inv_cancel]
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact fwd g hfw b hb
  · intro hb
    have h1 := fwd g⁻¹ hbw (g * b * g⁻¹) hb
    have e : g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b := by group
    rwa [e] at h1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6Delta

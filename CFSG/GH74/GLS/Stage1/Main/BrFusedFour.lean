module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedPkg
public import CFSG.GH74.GLS.Stage1.Main.BrBaseModel
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74 CFSG.GH74.GLS
  CFSG.GH74.GLS.LU.Local CFSG.GorensteinWalter
open scoped commutatorElement

section Abstract

variable {X : Type} [Group X]

theorem fusedPGL_no_commute [Finite X] {z : X}
    {E : Subgroup X} {n : X} {q : ℕ} (hodd : Odd q) (h3 : 3 < q) (hF : FusedPGL z E n q)
    (hperf : Group.IsPerfect ↥E) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzE : z ∈ E)
    (hzc : ∀ y ∈ E, y * z = z * y)
    (hcen : ∀ x ∈ E, (∀ y ∈ E, y * x = x * y) → x ∈ zpowers z) {a b : X} (haE : a ∈ E) (hbE : b ∈ E)
    (haa : a * a = z) (hbb : b * b = z) (hba : b * a = z * (a * b)) {e : X} (heE : e ∈ E)
    (hca : (e * n) * a * (e * n)⁻¹ = a ∨ (e * n) * a * (e * n)⁻¹ = z * a)
    (hcb : (e * n) * b * (e * n)⁻¹ = b ∨ (e * n) * b * (e * n)⁻¹ = z * b) : False := by
  classical
  obtain ⟨Z, hZC, hZB, hzZ, -, hn, hP⟩ := hF
  have hP' := hP
  obtain ⟨F₀, iF, fF, hq, ⟨φ⟩⟩ := hP
  set B : Subgroup X := E ⊔ zpowers n with hBdef
  have hEB : E ≤ B := le_sup_left
  have hnB : n ∈ B := Subgroup.mem_sup_right (mem_zpowers n)
  have := hn
  set π : ↥B →* (↥B ⧸ Z.subgroupOf B) := QuotientGroup.mk' (Z.subgroupOf B) with hπ
  have hmk : ∀ (g : X) (hg : g ∈ B), π ⟨g, hg⟩ = 1 ↔ g ∈ Z := by
    intro g hg
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hZc : ∀ g ∈ Z, ∀ y ∈ E, y * g = g * y := fun g hg y hy =>
    Subgroup.mem_centralizer_iff.1 (hZC hg) y hy
  have hnotZ : ∀ g : X, g ∈ E → g * g = z → g ∉ Z := by
    intro g hgE hgg hgZ
    have hgz : g ∈ zpowers z := hcen g hgE (hZc g hgZ)
    rcases eq_one_or_eq_of_mem_zpowers_sq hz2 hgz with h1 | h1
    · rw [h1, mul_one] at hgg
      exact hz1 hgg.symm
    · rw [h1, hz2] at hgg
      exact hz1 hgg.symm
  have hzZ' : ∀ (g : X), g = z → ∀ hg : g ∈ B, π ⟨g, hg⟩ = 1 := fun g hg hgB => by
    rw [hmk]; rw [hg]; exact hzZ
  set a' : ↥B := ⟨a, hEB haE⟩ with ha'
  set b' : ↥B := ⟨b, hEB hbE⟩ with hb'
  set c' : ↥B := ⟨e * n, B.mul_mem (hEB heE) hnB⟩ with hc'
  have hxx : π a' * π a' = 1 := by
    rw [← map_mul]
    have : a' * a' = ⟨z, hEB hzE⟩ := Subtype.ext haa
    rw [this]
    exact hzZ' z rfl _
  have hyy : π b' * π b' = 1 := by
    rw [← map_mul]
    have : b' * b' = ⟨z, hEB hzE⟩ := Subtype.ext hbb
    rw [this]
    exact hzZ' z rfl _
  have hx1 : π a' ≠ 1 := fun h1 => hnotZ a haE haa ((hmk a _).1 h1)
  have hy1 : π b' ≠ 1 := fun h1 => hnotZ b hbE hbb ((hmk b _).1 h1)
  have hxo : orderOf (π a') = 2 := orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  have hyo : orderOf (π b') = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
  have hxy : π a' * π b' = π b' * π a' := by
    have h1 : b' * a' = ⟨z, hEB hzE⟩ * (a' * b') := Subtype.ext hba
    have h2 : π (b' * a') = π (a' * b') := by
      rw [h1, map_mul, hzZ' z rfl _, one_mul]
    rw [← map_mul, ← map_mul]
    exact h2.symm
  have hne : π a' ≠ π b' := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have h2 : a⁻¹ * b ∈ Z := h1
    have h3 : a⁻¹ * b ∈ zpowers z :=
      hcen _ (E.mul_mem (E.inv_mem haE) hbE) (hZc _ h2)
    have hcab : b * a = a * b := by
      rcases eq_one_or_eq_of_mem_zpowers_sq hz2 h3 with h4 | h4
      · have hb'' : b = a := by
          calc b = a * (a⁻¹ * b) := by group
            _ = a := by rw [h4, mul_one]
        rw [hb'']
      · have hb'' : b = a * z := by
          calc b = a * (a⁻¹ * b) := by group
            _ = a * z := by rw [h4]
        rw [hb'']
        calc a * z * a = a * (z * a) := by group
          _ = a * (a * z) := by rw [← hzc a haE]
    have hab : a * b = z * (a * b) := by
      calc a * b = b * a := hcab.symm
        _ = z * (a * b) := hba
    exact hz1 (mul_right_cancel (show z * (a * b) = 1 * (a * b) by rw [one_mul]; exact hab.symm))
  have hcomm_aux : ∀ (g : X) (hgE : g ∈ E), ((e * n) * g * (e * n)⁻¹ = g ∨ (e * n) * g * (e * n)⁻¹ = z * g) →
      π c' * π ⟨g, hEB hgE⟩ = π ⟨g, hEB hgE⟩ * π c' := by
    intro g hgE hg
    rw [← map_mul, ← map_mul]
    rcases hg with h1 | h1
    · have h2 : (e * n) * g = g * (e * n) := by
        calc (e * n) * g = ((e * n) * g * (e * n)⁻¹) * (e * n) := by group
          _ = g * (e * n) := by rw [h1]
      have : c' * (⟨g, hEB hgE⟩ : ↥B) = ⟨g, hEB hgE⟩ * c' := Subtype.ext h2
      rw [this]
    · have h2 : (e * n) * g = z * (g * (e * n)) := by
        calc (e * n) * g = ((e * n) * g * (e * n)⁻¹) * (e * n) := by group
          _ = z * g * (e * n) := by rw [h1]
          _ = z * (g * (e * n)) := by group
      have : c' * (⟨g, hEB hgE⟩ : ↥B) = ⟨z, hEB hzE⟩ * (⟨g, hEB hgE⟩ * c') := Subtype.ext h2
      rw [this, map_mul, hzZ' z rfl _, one_mul]
  have hcx := hcomm_aux a haE hca
  have hcy := hcomm_aux b hbE hcb
  have hcl := kfour_apply hodd hP' hxo hyo hxy hne hcx hcy
  set E' : Subgroup ↥B := E.subgroupOf B with hE'
  have hcl' : π c' ∈ E'.map π := by
    have hle : Subgroup.closure ({π a', π b'} : Set (↥B ⧸ Z.subgroupOf B)) ≤ E'.map π := by
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact ⟨a', haE, rfl⟩
      · exact ⟨b', hbE, rfl⟩
    exact hle hcl
  let ρ : ↥B →* PGL2 F₀ := φ.toMonoidHom.comp π
  have hρsurj : Function.Surjective ρ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  set R : Subgroup (PGL2 F₀) := E'.map ρ with hR
  have hE'perf : ⁅E', E'⁆ = E' := by
    have hperf' : Group.IsPerfect ↥E' :=
      Group.IsPerfect.ofSurjective (G := ↥E) (G' := ↥E')
        (f := (Subgroup.subgroupOfEquivOfLe hEB).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hEB).symm.surjective
    exact Subgroup.isPerfect_iff.1 hperf'
  have hRperf : ⁅R, R⁆ = R := by
    rw [hR, ← Subgroup.map_commutator, hE'perf]
  have hcR : ρ c' ∈ R := by
    obtain ⟨e', he', hec⟩ := hcl'
    exact ⟨e', he', by show φ (π e') = φ (π c'); rw [hec]⟩
  set L : Subgroup ↥B := R.comap ρ with hL
  have hE'L : E' ≤ L := fun x hx => ⟨x, hx, rfl⟩
  have hc'L : c' ∈ L := hcR
  have he'' : (⟨e, hEB heE⟩ : ↥B) ∈ E' := heE
  have hn'L : (⟨n, hnB⟩ : ↥B) ∈ L := by
    have : (⟨n, hnB⟩ : ↥B) = (⟨e, hEB heE⟩ : ↥B)⁻¹ * c' := by
      apply Subtype.ext
      show n = e⁻¹ * (e * n)
      group
    rw [this]
    exact L.mul_mem (L.inv_mem (hE'L he'')) hc'L
  have hLtop : L = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : g.1 ∈ E ⊔ zpowers n := g.2
    have hM : E ⊔ zpowers n ≤ L.map B.subtype := by
      refine sup_le ?_ ?_
      · intro x hx
        exact ⟨⟨x, hEB hx⟩, hE'L hx, rfl⟩
      · rw [Subgroup.zpowers_le]
        exact ⟨⟨n, hnB⟩, hn'L, rfl⟩
    obtain ⟨l, hl, hlg⟩ := hM hg
    have : l = g := Subtype.ext hlg
    rw [← this]
    exact hl
  have hRtop : R = ⊤ := by
    have h1 := Subgroup.map_comap_eq_self_of_surjective hρsurj R
    rw [← hL, hLtop, Subgroup.map_top, MonoidHom.range_eq_top.2 hρsurj] at h1
    exact h1.symm
  have hFodd : Odd (Nat.card F₀) := by rw [hq]; exact hodd
  have hFop := CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hFodd
  have hF3 : 3 < Nat.card F₀ := by rw [hq]; exact h3
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three F₀ hFop hF3
  rw [hRtop] at hRperf
  have hcom : commutator (PGL2 F₀) = ⊤ := by rw [commutator_def]; exact hRperf
  rw [hcomm] at hcom
  have hidx := pgl2_psl2Range_index_eq_two F₀ hFop
  rw [hcom, Subgroup.index_top] at hidx
  omega

end Abstract

section Model

variable {Gs : Type} [Group Gs] [Finite Gs] {q : ℕ} {ε : ℤ} {z' : Gs} {S' : Sylow 2 Gs}
  {E₁ E₂ : Subgroup Gs} {t' u' n' : Gs}

omit [Finite Gs] in
theorem comm_of_center {S : Subgroup Gs} {z : Gs} (hc : (center ↥S).map S.subtype = zpowers z) :
    z ∈ S ∧ ∀ x ∈ S, x * z = z * x := by
  have hmem : z ∈ (center ↥S).map S.subtype := by rw [hc]; exact mem_zpowers z
  obtain ⟨c, hc', hcz⟩ := hmem
  have hcz' : (c : Gs) = z := hcz
  refine ⟨hcz' ▸ c.2, fun x hx => ?_⟩
  have := Subgroup.mem_center_iff.1 hc' ⟨x, hx⟩
  rw [← hcz']
  exact congrArg Subtype.val this

theorem FusedPkg.E_le_normalizer₁ (h : FusedPkg Gs q ε z' S' E₁ E₂ t' u' n') :
    E₁ ⊔ E₂ ≤ normalizer (E₁ : Set Gs) := by
  intro y hy
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' h.data.comps.comm hy
  have h1 : e₁ ∈ normalizer (E₁ : Set Gs) := Subgroup.le_normalizer he₁
  have h2 : e₂ ∈ normalizer (E₁ : Set Gs) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact h.data.comps.comm g hg e₂ he₂
  exact mul_mem h1 h2

theorem FusedPkg.E_le_normalizer₂ (h : FusedPkg Gs q ε z' S' E₁ E₂ t' u' n') :
    E₁ ⊔ E₂ ≤ normalizer (E₂ : Set Gs) := by
  intro y hy
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' h.data.comps.comm hy
  have h1 : e₂ ∈ normalizer (E₂ : Set Gs) := Subgroup.le_normalizer he₂
  have h2 : e₁ ∈ normalizer (E₂ : Set Gs) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (h.data.comps.comm e₁ he₁ g hg).symm
  exact mul_mem h2 h1

theorem FusedPkg.exists_invol_outside (h : FusedPkg Gs q ε z' S' E₁ E₂ t' u' n') :
    ∃ t ∈ (S' : Subgroup Gs), orderOf t = 2 ∧ t ∉ E₁ ⊔ E₂ := by
  have hc := h.data.comps
  have hs := h.data.syl
  refine ⟨t', hs.t_mem, ?_, ?_⟩
  · obtain ⟨c, hc'⟩ := isConj_iff.1 hs.t_conj
    have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z'
    rw [MulAut.conj_apply, hc'] at h1
    rw [h1]
    exact hs.z_inv
  · intro hE
    have h1 : E₁.map (MulAut.conj t').toMonoidHom = E₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (h.E_le_normalizer₁ hE)
    apply hc.ne
    rw [← h1, hs.t_swap]

omit [Finite Gs] in
theorem FusedPkg.t_not_normalizer₁ (h : FusedPkg Gs q ε z' S' E₁ E₂ t' u' n') :
    t' ∉ normalizer (E₁ : Set Gs) := by
  intro ht
  have h1 : E₁.map (MulAut.conj t').toMonoidHom = E₁ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 ht
  apply h.data.comps.ne
  rw [← h1, h.data.syl.t_swap]

theorem FusedPkg.four_le
    (h : FusedPkg Gs q ε z' S' E₁ E₂ t' u' n') (hodd : Odd q) (h5 : 5 ≤ q)
    {V : Subgroup Gs} (hVS : V ≤ (S' : Subgroup Gs)) (hV4 : IVK.IsFourSubgroup V)
    (hVn : ∀ s ∈ (S' : Subgroup Gs), ∀ v ∈ V, s * v * s⁻¹ ∈ V) : V ≤ E₁ ⊔ E₂ := by
  classical
  have hc := h.data.comps
  have hs := h.data.syl
  have hSp : IsPGroup 2 ↥(S' : Subgroup Gs) := S'.isPGroup'
  obtain ⟨hz'S, hz'c⟩ := comm_of_center hs.z_cen
  have hz'o : orderOf z' = 2 := hs.z_inv
  have hsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'o, pow_two] at this
  have hz'1 : z' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz'o
    omega
  have hz'C : (S' : Subgroup Gs) ≤ centralizer ({z'} : Set Gs) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hz'c x hx)
  have hsyl' : CFSG.ABGLocalTools.IsSylowOf 2 (S' : Subgroup Gs) (centralizer ({z'} : Set Gs)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hz'C, hSp, fun hdvd => ?_⟩
    exact S'.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hz'C))
  have hz'E : z' ∈ E₁ ⊔ E₂ := Subgroup.mem_sup_left hc.z_mem₁
  intro u huV
  by_contra huE
  have hz'V : z' ∈ V := z_mem_four hSp hVS hV4 hVn hs.z_cen hsq
  have hu1 : u ≠ 1 := fun h1 => huE (h1 ▸ one_mem _)
  have huz : u ≠ z' := fun h1 => huE (h1 ▸ hz'E)
  have hu2 : u * u = 1 := by
    have : IsElementaryAbelian 2 ↥V := hV4.1
    have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) u huV
    rwa [pow_two] at h2
  have hcomm := four_conj hz'V huV hV4 hsq hz'1 hu1 huz hVn hz'c
  obtain ⟨a, haS, haE, b, hbS, hbE, haa, hbb, hba⟩ :=
    quat_pair_in_sylow hodd hsyl' hc.sl₁ hsq hz'1 hc.inf_eq hc.comm h.layer
  have huS : u ∈ (S' : Subgroup Gs) := hVS huV
  have huC : u ∈ centralizer ({z'} : Set Gs) := hz'C huS
  rcases hc.perm huC with ⟨hfix1, -⟩ | ⟨hswap, -⟩
  ·
    have hun₁ : u ∈ normalizer (E₁ : Set Gs) := mem_normalizer_of_map_eq hfix1
    obtain ⟨k, hk, hcases⟩ := h.dec u huS
    have hkE : k ∈ E₁ ⊔ E₂ := hk.2
    have hkn₁ : k ∈ normalizer (E₁ : Set Gs) := h.E_le_normalizer₁ hkE
    have hnn₁ : n' ∈ normalizer (E₁ : Set Gs) := h.n_norm₁
    rcases hcases with h1 | h1 | h1 | h1
    · exact huE (h1 ▸ hkE)
    · apply h.t_not_normalizer₁
      have : t' = k⁻¹ * u := by rw [h1]; group
      rw [this]
      exact mul_mem (inv_mem hkn₁) hun₁
    ·
      obtain ⟨e₁, he₁, e₂, he₂, hk'⟩ :=
        CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hc.comm hkE
      have hux : ∀ x ∈ (S' : Subgroup Gs), u * x * u⁻¹ = x ∨ u * x * u⁻¹ = z' * x := by
        intro x hx
        have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
        rcases hcomm x hx with h2 | h2
        · left
          have h' : x * u = u * x := by
            calc x * u = (x * u * x⁻¹) * x := by group
              _ = u * x := by rw [h2]
          rw [← h']
          group
        · right
          have h' : x * u = u * z' * x := by
            calc x * u = (x * u * x⁻¹) * x := by group
              _ = u * z' * x := by rw [h2]
          calc u * x * u⁻¹ = u * x * u := by rw [huinv]
            _ = u * (x * u) := by group
            _ = u * (u * z' * x) := by rw [h']
            _ = (u * u) * z' * x := by group
            _ = z' * x := by rw [hu2, one_mul]
      have hact : ∀ x ∈ E₁, u * x * u⁻¹ = (e₁ * n') * x * (e₁ * n')⁻¹ := by
        intro x hx
        have hy : n' * x * n'⁻¹ ∈ E₁ := (Subgroup.mem_normalizer_iff.1 hnn₁ x).1 hx
        have h2 : e₂ * (n' * x * n'⁻¹) * e₂⁻¹ = n' * x * n'⁻¹ := by
          have := hc.comm _ hy e₂ he₂
          calc e₂ * (n' * x * n'⁻¹) * e₂⁻¹ = (e₂ * (n' * x * n'⁻¹)) * e₂⁻¹ := by group
            _ = ((n' * x * n'⁻¹) * e₂) * e₂⁻¹ := by rw [← this]
            _ = n' * x * n'⁻¹ := by group
        calc u * x * u⁻¹ = e₁ * (e₂ * (n' * x * n'⁻¹) * e₂⁻¹) * e₁⁻¹ := by rw [h1, hk']; group
          _ = e₁ * (n' * x * n'⁻¹) * e₁⁻¹ := by rw [h2]
          _ = (e₁ * n') * x * (e₁ * n')⁻¹ := by group
      have hca : (e₁ * n') * a * (e₁ * n')⁻¹ = a ∨ (e₁ * n') * a * (e₁ * n')⁻¹ = z' * a := by
        rw [← hact a haE]
        exact hux a haS
      have hcb : (e₁ * n') * b * (e₁ * n')⁻¹ = b ∨ (e₁ * n') * b * (e₁ * n')⁻¹ = z' * b := by
        rw [← hact b hbE]
        exact hux b hbS
      refine fusedPGL_no_commute hodd (by omega) h.pgl hc.quasi₁.1 hsq hz'1 hc.z_mem₁
        (fun y hy => hc.cz₁ hy) ?_ haE hbE haa hbb hba he₁ hca hcb
      intro x hx hxc
      have hxm : x ∈ (center ↥E₁).map E₁.subtype :=
        Subgroup.mem_map.2 ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 (fun g => Subtype.ext (hxc g g.2)), rfl⟩
      rw [hc.cen₁] at hxm
      exact hxm
    · apply h.t_not_normalizer₁
      have : t' = k⁻¹ * u * n'⁻¹ := by rw [h1]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hkn₁) hun₁) (inv_mem hnn₁)
  ·
    exact swap_case_false hc.inf_eq hsq hz'1 hc.z_mem₁ haS haE haa hu2 hswap hcomm

end Model

end CFSG.GH74.GLS.Stage1.Main

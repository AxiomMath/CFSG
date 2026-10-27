module

public import CFSG.GH74.Generic.BProg.B3.S3T2Loc28
public import CFSG.GH74.Generic.BProg.B2.Thm2Comp
public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC2
public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC3
public import CFSG.GH74.Generic.BProg.B2.Prop31
public import CFSG.GH74.Generic.BProg.B2.ListedG5
public import CFSG.GH74.Generic.BProg.B2.T4OutComm

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

namespace S3T4

variable {G : Type} [Group G] [Finite G]

theorem mk_mem_centralizer_barIn {M K : Subgroup G} (hKM : K ≤ M)
    (hq : IsQuasisimple ↥(barIn M K)) {b : G} (hbM : b ∈ M)
    (hb : b ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    ∀ k ∈ barIn M K, k * (QuotientGroup.mk (⟨b, hbM⟩ : ↥M) : Mbar M) =
      (QuotientGroup.mk (⟨b, hbM⟩ : ↥M) : Mbar M) * k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup (Mbar M) := barIn M K with hL
  set f : ↥K →* ↥L := S3T2.toBar hKM with hf
  have hfs : Function.Surjective f := S3T2.toBar_surjective hKM
  have hN : ((pPrimeCore 2 ↥K).map f).Normal := (pPrimeCore_normal (p := 2)).map f hfs
  have hZ : (pPrimeCore 2 ↥K).map f ≤ center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hle
    · exfalso
      have hodd : Odd (Nat.card ↥L) := by
        have h1 : Nat.card ↥L = Nat.card ↥((pPrimeCore 2 ↥K).map f) := by
          rw [htop, Subgroup.card_top]
        rw [h1]
        exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
          (Subgroup.card_map_dvd (pPrimeCore 2 ↥K) f)
          (pPrimeCore_coprime_card (p := 2) (G := ↥K)))
      have hsol : Group.IsSolvable ↥L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect ↥L := hq.1
      exact Group.IsPerfect.not_isSolvable ↥L hsol
    · exact hle
  set q : Mbar M := QuotientGroup.mk (⟨b, hbM⟩ : ↥M) with hq'
  have hcomm : ∀ k ∈ L, ⁅k, q⁆ ∈ L ∧ ∀ k' ∈ L, ⁅k, q⁆ * k' = k' * ⁅k, q⁆ := by
    rintro _ ⟨m, hm, rfl⟩
    have hmK : (m : G) ∈ K := Subgroup.mem_subgroupOf.1 hm
    obtain ⟨o, ho, hoe⟩ := hb.2.2 _ hmK
    have hfo : ((f o : ↥L) : Mbar M) = ⁅QuotientGroup.mk' (pPrimeCore 2 ↥M) m, q⁆ := by
      rw [hq', ← QuotientGroup.mk'_apply, ← map_commutatorElement]
      show QuotientGroup.mk' (pPrimeCore 2 ↥M) (Subgroup.inclusion hKM o) = _
      congr 1
      apply Subtype.ext
      exact hoe
    have hcen := Subgroup.mem_center_iff.1 (hZ ⟨o, ho, rfl⟩)
    refine ⟨hfo ▸ (f o).2, fun k' hk' => ?_⟩
    have h1 := congrArg Subtype.val (hcen ⟨k', hk'⟩)
    rw [← hfo]
    exact h1.symm
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hq.1
  exact B2.Thm2Comp.commute_of_commutator_central hperf (fun k hk => (hcomm k hk).1)
    (fun k hk k' hk' => (hcomm k hk).2 k' hk')

theorem eq_one_of_central_sup {X : Type} [Group X] {L₁ L₂ : Subgroup X}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h1 : center ↥L₁ = ⊥) (h2 : center ↥L₂ = ⊥)
    {z : X} (hz : z ∈ L₁ ⊔ L₂) (hzc : ∀ w ∈ L₁ ⊔ L₂, w * z = z * w) : z = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (B2.Thm2AssemblyC3.mem_sup_iff hc).1 hz
  have ha1 : a = 1 := by
    have hmem : (⟨a, ha⟩ : ↥L₁) ∈ center ↥L₁ := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have e1 := hzc l (Subgroup.mem_sup_left l.2)
      have e2 := hc l l.2 b hb
      show (l : X) * a = a * l
      have : (l : X) * a * b = a * l * b := by
        calc (l : X) * a * b = l * (a * b) := by group
          _ = a * b * l := e1
          _ = a * (b * l) := by group
          _ = a * (l * b) := by rw [e2]
          _ = a * l * b := by group
      exact mul_right_cancel this
    rw [h1, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hb1 : b = 1 := by
    have hmem : (⟨b, hb⟩ : ↥L₂) ∈ center ↥L₂ := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have e1 := hzc l (Subgroup.mem_sup_right l.2)
      have e2 := hc a ha l l.2
      show (l : X) * b = b * l
      have : a * (l * b) = a * (b * l) := by
        calc a * (l * b) = (a * l) * b := by group
          _ = (l * a) * b := by rw [e2]
          _ = l * (a * b) := by group
          _ = a * b * l := e1
          _ = a * (b * l) := by group
      exact mul_left_cancel this
    rw [h2, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  rw [ha1, hb1, mul_one]

theorem eq_one_or_eq_of_swap {X : Type} [Group X] [Finite X] {t g : X} {L₁ L₂ : Subgroup X}
    (hFit : generalizedFitting X = L₁ ⊔ L₂) (hL₁ : IsComponent L₁) (hL₂ : IsComponent L₂)
    (hne : L₁ ≠ L₂) (hs₁ : IsSimpleGroup ↥L₁) (hs₂ : IsSimpleGroup ↥L₂) (ht : t * t = 1)
    (hconj : L₁.map (MulAut.conj t).toMonoidHom = L₂)
    (hall : ∀ L : Subgroup X, IsComponent L → L = L₁ ∨ L = L₂) {Kb : Subgroup X}
    (hK : IsCompIn (centralizer ({t} : Set X)) Kb) (hKL : Kb ≤ L₁ ⊔ L₂) (hgt : g * t = t * g)
    (hgK : ∀ k ∈ Kb, k * g = g * k) : g = 1 ∨ g = t := by
  classical
  have hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
    intro a ha b hb
    have hle : L₁ ≤ centralizer (L₂ : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((CFSG.LocalCores.distinct_components_commute hL₁ hL₂).resolve_left hne)
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm
  have hZ1 : center ↥L₁ = ⊥ := B2.Thm2AssemblyC3.center_eq_bot_of_simple_quasisimple hL₁.1 hs₁
  have hZ2 : center ↥L₂ = ⊥ := B2.Thm2AssemblyC3.center_eq_bot_of_simple_quasisimple hL₂.1 hs₂
  have hcap : L₁ ⊓ L₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzc : (⟨z, hz.1⟩ : ↥L₁) ∈ center ↥L₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2 z hz.2)
    rw [hZ1, Subgroup.mem_bot] at hzc
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hzc)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htt : t⁻¹ * t⁻¹ = 1 := by rw [htinv, ht]
  have hconjt : ∀ g' y : X, g' * t = t * g' →
      g' * y * g'⁻¹ = t * (g' * (t * y * t⁻¹) * g'⁻¹) * t⁻¹ := by
    intro g' y h
    have h' : t⁻¹ * g'⁻¹ = g'⁻¹ * t⁻¹ := by rw [← mul_inv_rev, h, mul_inv_rev]
    calc g' * y * g'⁻¹ = t * t * (g' * y * g'⁻¹) * (t⁻¹ * t⁻¹) := by rw [ht, htt]; group
      _ = t * (t * g') * y * (g'⁻¹ * t⁻¹) * t⁻¹ := by group
      _ = t * (g' * t) * y * (t⁻¹ * g'⁻¹) * t⁻¹ := by rw [← h, ← h']
      _ = t * (g' * (t * y * t⁻¹) * g'⁻¹) * t⁻¹ := by group
  have h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂ := fun a ha => by
    rw [← hconj]
    exact ⟨a, ha, rfl⟩
  have h21 : ∀ b ∈ L₂, t * b * t⁻¹ ∈ L₁ := by
    intro b hb
    rw [← hconj] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have e : t * ((MulAut.conj t).toMonoidHom a) * t⁻¹ = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
        _ = a := by rw [ht, htt, one_mul, mul_one]
    rw [e]
    exact ha
  have hgD : ∀ d ∈ (L₁ ⊔ L₂) ⊓ centralizer ({t} : Set X), d * g = g * d := by
    obtain ⟨e⟩ := B2.Thm2AssemblyC3.mulEquiv_centralizer_of_swap ht hc hcap h12 h21
    have hNs : IsSimpleGroup ↥((L₁ ⊔ L₂) ⊓ centralizer ({t} : Set X)) := e.symm.isSimpleGroup
    have hKN := B2.Thm2AssemblyC3.eq_of_isCompIn_of_simple hNs
      (B2.Prop31.isCompIn_of_le (le_inf hKL hK.1) inf_le_right hK)
    exact fun d hd => hgK d (hKN ▸ hd)
  have htwice : ∀ y : X, t * (t * y * t⁻¹) * t⁻¹ = y := fun y => by
    calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
      _ = y := by rw [ht, htt, one_mul, mul_one]
  have key : ∀ g' : X, g' * t = t * g' →
      (∀ d ∈ (L₁ ⊔ L₂) ⊓ centralizer ({t} : Set X), d * g' = g' * d) →
      (∀ a ∈ L₁, g' * a * g'⁻¹ ∈ L₁) → g' = 1 := by
    intro g' hg't hg'D hg'N
    have hg'N2 : ∀ b ∈ L₂, g' * b * g'⁻¹ ∈ L₂ := fun b hb => by
      rw [hconjt g' b hg't]
      exact h12 _ (hg'N _ (h21 b hb))
    have hcentL₁ : ∀ a ∈ L₁, g' * a * g'⁻¹ = a := by
      intro a ha
      have hd : a * (t * a * t⁻¹) ∈ (L₁ ⊔ L₂) ⊓ centralizer ({t} : Set X) := by
        rw [← B2.Thm2AssemblyC3.range_diagHom ht hc hcap h12 h21]
        exact ⟨⟨a, ha⟩, rfl⟩
      have h1 := hg'D _ hd
      have h2 : (g' * a * g'⁻¹) * (g' * (t * a * t⁻¹) * g'⁻¹) = a * (t * a * t⁻¹) := by
        calc (g' * a * g'⁻¹) * (g' * (t * a * t⁻¹) * g'⁻¹)
            = g' * (a * (t * a * t⁻¹)) * g'⁻¹ := by group
          _ = (a * (t * a * t⁻¹)) * g' * g'⁻¹ := by rw [← h1]
          _ = a * (t * a * t⁻¹) := by group
      have hm1 : a⁻¹ * (g' * a * g'⁻¹) ∈ L₁ := L₁.mul_mem (L₁.inv_mem ha) (hg'N a ha)
      have hm2 : a⁻¹ * (g' * a * g'⁻¹) ∈ L₂ := by
        have e : a⁻¹ * (g' * a * g'⁻¹) =
            (t * a * t⁻¹) * (g' * (t * a * t⁻¹) * g'⁻¹)⁻¹ := by
          calc a⁻¹ * (g' * a * g'⁻¹)
              = a⁻¹ * ((g' * a * g'⁻¹) * (g' * (t * a * t⁻¹) * g'⁻¹)) *
                  (g' * (t * a * t⁻¹) * g'⁻¹)⁻¹ := by group
            _ = a⁻¹ * (a * (t * a * t⁻¹)) * (g' * (t * a * t⁻¹) * g'⁻¹)⁻¹ := by rw [h2]
            _ = (t * a * t⁻¹) * (g' * (t * a * t⁻¹) * g'⁻¹)⁻¹ := by group
        rw [e]
        exact L₂.mul_mem (h12 a ha) (L₂.inv_mem (hg'N2 _ (h12 a ha)))
      have h3 : a⁻¹ * (g' * a * g'⁻¹) ∈ L₁ ⊓ L₂ := ⟨hm1, hm2⟩
      rw [hcap, Subgroup.mem_bot] at h3
      exact (inv_mul_eq_one.1 h3).symm
    have hcentL₂ : ∀ b ∈ L₂, g' * b * g'⁻¹ = b := fun b hb => by
      rw [hconjt g' b hg't, hcentL₁ _ (h21 b hb), htwice]
    have hcomm : ∀ w ∈ L₁ ⊔ L₂, w * g' = g' * w := by
      intro w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := (B2.Thm2AssemblyC3.mem_sup_iff hc).1 hw
      have e1 : g' * a = a * g' := by
        calc g' * a = g' * a * g'⁻¹ * g' := by group
          _ = a * g' := by rw [hcentL₁ a ha]
      have e2 : g' * b = b * g' := by
        calc g' * b = g' * b * g'⁻¹ * g' := by group
          _ = b * g' := by rw [hcentL₂ b hb]
      calc a * b * g' = a * (g' * b) := by rw [mul_assoc, e2]
        _ = g' * a * b := by rw [← mul_assoc, ← e1]
        _ = g' * (a * b) := by rw [mul_assoc]
    have hg'F : g' ∈ L₁ ⊔ L₂ := by
      rw [← hFit]
      refine CFSG.centralizer_generalizedFitting_le X (Subgroup.mem_centralizer_iff.2 ?_)
      intro w hw
      rw [hFit] at hw
      exact hcomm w hw
    exact eq_one_of_central_sup hc hZ1 hZ2 hg'F hcomm
  have hcompg := CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent
    (MulAut.conj g) hL₁
  have hmemmap : ∀ a ∈ L₁, g * a * g⁻¹ ∈ L₁.map (MulAut.conj g).toMonoidHom :=
    fun a ha => ⟨a, ha, by simp⟩
  rcases hall _ hcompg with hfix | hswap
  · left
    refine key g hgt hgD fun a ha => ?_
    rw [← hfix]
    exact hmemmap a ha
  · right
    have hgN : ∀ a ∈ L₁, g * a * g⁻¹ ∈ L₂ := fun a ha => hswap ▸ hmemmap a ha
    have hgN2 : ∀ b ∈ L₂, g * b * g⁻¹ ∈ L₁ := fun b hb => by
      rw [hconjt g b hgt]
      exact h21 _ (hgN _ (h21 b hb))
    have hgtt : g * t * t = t * (g * t) := by
      calc g * t * t = t * g * t := by rw [hgt]
        _ = t * (g * t) := by rw [mul_assoc]
    have h1 : g * t = 1 := key (g * t) hgtt (fun d hd => by
        have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.1 hd.2
        calc d * (g * t) = (d * g) * t := by group
          _ = (g * d) * t := by rw [hgD d hd]
          _ = g * (d * t) := by group
          _ = g * (t * d) := by rw [hdt]
          _ = g * t * d := by group)
      (fun a ha => by
        have e : g * t * a * (g * t)⁻¹ = g * (t * a * t⁻¹) * g⁻¹ := by group
        rw [e]
        exact hgN2 _ (h12 a ha))
    calc g = g * t * t⁻¹ := by group
      _ = t⁻¹ := by rw [h1, one_mul]
      _ = t := htinv

theorem eq_of_mk_eq {M : Subgroup G} {a b : G} (ha : a ∈ M) (hb : b ∈ M) (hab : a * b = b * a)
    (ha2 : a * a = 1) (hb2 : b * b = 1)
    (h : (QuotientGroup.mk (⟨a, ha⟩ : ↥M) : Mbar M) = QuotientGroup.mk (⟨b, hb⟩ : ↥M)) :
    a = b := by
  have hmem := QuotientGroup.eq.1 h
  have hsq : ((⟨a, ha⟩ : ↥M)⁻¹ * ⟨b, hb⟩) * ((⟨a, ha⟩ : ↥M)⁻¹ * ⟨b, hb⟩) = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [hai]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have h1 := Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore hsq hmem
  have h2 : (⟨a, ha⟩ : ↥M) = ⟨b, hb⟩ := inv_mul_eq_one.1 h1
  exact congrArg Subtype.val h2

theorem shapeS3_barIn {M K : Subgroup G} (hKM : K ≤ M) (hq : IsQuasisimple ↥(barIn M K))
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) : B2.T4.ShapeS3 (barIn M K) := by
  let φ : ↥K →* ↥(barIn M K) :=
    ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hKM)).codRestrict (barIn M K)
      (fun k => ⟨Subgroup.inclusion hKM k, k.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  have hker : φ.ker ≤ pPrimeCore 2 ↥K :=
    (MonoidHom.ker_codRestrict _ _ _).le.trans (B2.Prop31.ker_le_pPrimeCore hKM)
  obtain ⟨Z, hZ, hodd, ⟨e⟩⟩ := B2.Prop31.exists_odd_quotient_equiv φ hφs hker
  exact ⟨Z, B2.Prop31.normal_le_center_of_odd hq hZ hodd, hodd, hZ, S3T2.qShape3_of_mulEquiv e h3⟩

theorem exists_shape_barIn {M K : Subgroup G} (hKM : K ≤ M) (hq : IsQuasisimple ↥(barIn M K))
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ Z : Subgroup ↥(barIn M K), Z ≤ center ↥(barIn M K) ∧ Odd (Nat.card ↥Z) ∧
      ∃ _ : Z.Normal, QShapeNS (↥(barIn M K) ⧸ Z) := by
  obtain ⟨Z, hZc, hodd, hZ, hsh⟩ := shapeS3_barIn hKM hq h3
  exact ⟨Z, hZc, hodd, hZ, Or.inr (Or.inl hsh)⟩

theorem barIn_nonabelian {x : G} {M K H : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hKM : K ≤ M)
    (hF : barIn M H = generalizedFitting (Mbar M)) (hsimple : IsSimpleGroup ↥(barIn M H)) :
    ∃ a b : ↥(barIn M H), a * b ≠ b * a := by
  by_contra hcon
  have hcomm : ∀ a b : ↥(barIn M H), a * b = b * a := fun a b => by
    by_contra h
    exact hcon ⟨a, b, h⟩
  have hsolvbar : Group.IsSolvable (Mbar M) :=
    B2.GHTrichotomy.isSolvable_of_eq_generalizedFitting hF hsimple hcomm
  have hsolvM : Group.IsSolvable ↥M := B2.GHTrichotomy.isSolvable_of_quotient_pPrimeCore hsolvbar
  have hsolvK : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKM)
      (Subgroup.inclusion_injective hKM)
  exact B2.GHTrichotomy.not_isSolvable_of_isQuasisimple (TwoThin.isQuasisimple_hat hK)
    inferInstance

end S3T4

open S3T4

@[expose] def Leaf514Fam (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H L : Subgroup N) (v w : N), SectionalTwoRankLE N 4 →
    P ↥H → B2.T4.ShapeS3 L → v * w = w * v → v ≠ w → B2.ShapeInCent H v L →
    B2.ShapeInCent H w L → B2.ShapeInCent H (v * w) L → False

@[expose] def Leaf514S3 : Prop :=
  Leaf514Fam (fun X _ => B2.PuL5 X) ∧ Leaf514Fam (fun X _ => B2.TA7.PuL4m X) ∧
    Leaf514Fam (fun X _ => B2.PuL3sq X) ∧ Leaf514Fam (fun X _ => B2.PuG2Odd X)

theorem h175_of (hB2 : B_B2_g4) (hPump : B2.PumpupTableU) (hL4m : B2.TA7.RefinePuL4)
    (hG2 : B2.TA7.RefinePuG2) (hLeaf : Leaf514S3) {G : Type} [Group G] [Finite G] :
    ∀ (x : G) (K A B M H : Subgroup G), Hyp2 G → IsTwoTerminal x K →
      QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B →
      pRank 2 ↥B = 4 → M ≠ ⊤ → K ≤ M → gammaK 2 B 3 ≤ M → IsMinSubnormalIn K M H →
      barIn M H ≠ barIn M K → B ⊓ centralizerSection K (pPrimeCoreOf 2 K) ≤ zpowers x := by
  classical
  intro x K A B M H hyp ht h3 _ hext hB4 hM hKM hΓ hH hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hILo : IsILo 2 x K := ht.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hx2 : orderOf x = 2 := hILo.1
  obtain ⟨-, hxB, hBC, hBel, -, -, -⟩ := hext
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hBM : B ≤ M := (S3Boot152.le_gammaK_self hBel (by rw [hB4]; norm_num)).trans hΓ
  have hxM : x ∈ M := hBM hxB
  have hcomp := B2.barIn_K_isCompIn_gen hB2 hyp hM hILo hKM hxM
  have hKq : IsQuasisimple ↥(barIn M K) := B2.Prop31.isQuasisimple_of_isCompIn hcomp
  have hbarKH : barIn M K ≤ barIn M H := Subgroup.map_mono (Subgroup.comap_mono hH.1)
  have hxK : x ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
    C3.Layer1.Back.mem_centralizerSection_of_centralizes
      (fun _ hk => (Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hk)).symm)
      Th2Sig6.pPrimeCoreOf_le
  have hxx : x * x = 1 := hBsq x hxB
  set xb : Mbar M := QuotientGroup.mk (⟨x, hxM⟩ : ↥M) with hxbdef
  have hxb2 : orderOf xb = 2 := B2.Prop31.orderOf_mk_involution hxM hx2
  intro b hb
  obtain ⟨hbB, hbK⟩ := Subgroup.mem_inf.1 hb
  have hbM : b ∈ M := hBM hbB
  have hbb : b * b = 1 := hBsq b hbB
  have hxbc : x * b = b * x := hBc x hxB b hbB
  set bb : Mbar M := QuotientGroup.mk (⟨b, hbM⟩ : ↥M) with hbbdef
  have hbcen := mk_mem_centralizer_barIn hKM hKq hbM hbK
  have hcomm : bb * xb = xb * bb := by
    rw [hbbdef, hxbdef, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hxbc.symm
  rcases B2.lemma119_gen hB2 hyp hM hILo ht hKM hxM hH with hc1 | ⟨hF, hsimple⟩ |
      ⟨hF, hx, L₁, L₂, hL₁, hL₂, hneL, hs₁, hs₂, hsup, hconj, hall⟩
  · exact absurd hc1 hne
  ·
    by_contra hbx
    have hb1 : b ≠ 1 := fun h1 => hbx (h1 ▸ Subgroup.one_mem _)
    have hbx' : b ≠ x := fun h1 => hbx (h1 ▸ Subgroup.mem_zpowers x)
    have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hbb) hb1
    have hnonab := barIn_nonabelian hK hKM hF hsimple
    have hSh : B2.ShapeInCent (barIn M H) xb (barIn M K) :=
      { normal := by
          rw [hF]
          exact (CFSG.LocalCores.generalized_fitting_characteristic).2
        simple := hsimple
        faithful := B2.Thm2AssemblyC2.faithful_of_simple hF hsimple hnonab
        inv := hxb2
        comp := B2.Prop31.isCompIn_of_le (le_inf hbarKH hcomp.1) inf_le_right hcomp
        shape := exists_shape_barIn hKM hKq h3 }
    have hGH : GHList ↥(barIn M H) :=
      GLS.IVK.ghList_of_subgroup_of_quotient hyp.kgh hM (QuotientGroup.mk' (pPrimeCore 2 ↥M))
        (QuotientGroup.mk'_surjective _) (barIn M H) hsimple hnonab
    have h4 : SectionalTwoRankLE (Mbar M) 4 :=
      Gen4.quotient (pPrimeCore 2 ↥M) (Gen4.subgroup M hyp.gen4)
    have hPT : B2.PuTargetG4 ↥(barIn M H) := by
      rcases hPump (Mbar M) (barIn M H) _ (barIn M K) hSh hGH with h5 | h4' | h3' | hg
      · exact Or.inl h5
      · exact Or.inr (Or.inl (hL4m (Mbar M) (barIn M H) _ (barIn M K) hSh h4 h4'))
      · exact Or.inr (Or.inr (Or.inl h3'))
      · exact Or.inr (Or.inr (Or.inr (hG2 (Mbar M) (barIn M H) _ (barIn M K) hSh hg)))
    have hbC : b ∈ CxK x K := Subgroup.mem_inf.2 ⟨hBC hbB, hbK⟩
    have hcb := B2.barIn_K_isCompIn_at hB2 hyp hM hILo ht hKM hKq hbC hb2 hbM
      (Subgroup.mem_centralizer_iff.2 hbcen)
    have hxbM : x * b ∈ M := mul_mem hxM hbM
    have hxbK : x * b ∈ centralizerSection K (pPrimeCoreOf 2 K) := mul_mem hxK hbK
    have hxbC : x * b ∈ CxK x K :=
      Subgroup.mem_inf.2 ⟨mul_mem (Subgroup.mem_centralizer_singleton_iff.2 rfl) (hBC hbB), hxbK⟩
    have hxb1 : x * b ≠ 1 := fun h1 => hbx' (by
      have := eq_inv_of_mul_eq_one_right h1
      rw [this, inv_eq_of_mul_eq_one_right hxx])
    have hxbo : orderOf (x * b) = 2 := by
      refine orderOf_eq_prime ?_ hxb1
      rw [sq]
      calc x * b * (x * b) = x * (b * x) * b := by group
        _ = x * (x * b) * b := by rw [hxbc]
        _ = (x * x) * (b * b) := by group
        _ = 1 := by rw [hxx, hbb, one_mul]
    have hcxb := B2.barIn_K_isCompIn_at hB2 hyp hM hILo ht hKM hKq hxbC hxbo hxbM
      (Subgroup.mem_centralizer_iff.2 (mk_mem_centralizer_barIn hKM hKq hxbM hxbK))
    have hmul : (QuotientGroup.mk (⟨x * b, hxbM⟩ : ↥M) : Mbar M) = xb * bb := by
      rw [hxbdef, hbbdef, ← QuotientGroup.mk_mul]
      rfl
    have hxbo' := B2.Prop31.orderOf_mk_involution hxbM hxbo
    rw [hmul] at hcxb hxbo'
    have hShb : B2.ShapeInCent (barIn M H) bb (barIn M K) :=
      { hSh with
        inv := B2.Prop31.orderOf_mk_involution hbM hb2
        comp := B2.Prop31.isCompIn_of_le (le_inf hbarKH hcb.1) inf_le_right hcb }
    have hShxb : B2.ShapeInCent (barIn M H) (xb * bb) (barIn M K) :=
      { hSh with
        inv := hxbo'
        comp := B2.Prop31.isCompIn_of_le (le_inf hbarKH hcxb.1) inf_le_right hcxb }
    have hne' : xb ≠ bb := fun h1 => hbx' (eq_of_mk_eq hbM hxM hxbc.symm hbb hxx h1.symm)
    have hS3 := shapeS3_barIn hKM hKq h3
    obtain ⟨hL5, hL4, hL3, hLG2⟩ := hLeaf
    rcases hPT with hP | hP | hP | hP
    · exact hL5 _ _ _ _ _ h4 hP hS3 hcomm.symm hne' hSh hShb hShxb
    · exact hL4 _ _ _ _ _ h4 hP hS3 hcomm.symm hne' hSh hShb hShxb
    · exact hL3 _ _ _ _ _ h4 hP hS3 hcomm.symm hne' hSh hShb hShxb
    · exact hLG2 _ _ _ _ _ h4 hP hS3 hcomm.symm hne' hSh hShb hShxb
  ·
    have ht2 : xb * xb = 1 := by
      have := pow_orderOf_eq_one xb
      rwa [hxb2, pow_two] at this
    have hFit : generalizedFitting (Mbar M) = L₁ ⊔ L₂ := hF.symm.trans hsup
    rcases eq_one_or_eq_of_swap hFit hL₁ hL₂ hneL hs₁ hs₂ ht2 hconj hall hcomp
        (hsup ▸ hbarKH) hcomm hbcen with h1 | h1
    · have : b = 1 := eq_of_mk_eq hbM (one_mem M) (by group) hbb (by group) (by
        rw [← hbbdef, h1]
        rfl)
      rw [this]
      exact Subgroup.one_mem _
    · rw [eq_of_mk_eq hbM hxM hxbc.symm hbb hxx h1]
      exact Subgroup.mem_zpowers x

end CFSG.GH74.Generic.BProg.B3

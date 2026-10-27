module

public import CFSG.ClassicalInvolution.Sp62Rec.I1.ActionData
public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrE64
public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1
import CFSG.ClassicalInvolution.Sp62Rec.SylowOfHatAll

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec.I1

section Acts

variable {G : Type} [Group G] {e : G} {E : Subgroup G} {f : ↥E →* Wr 6}

theorem ActsOnE.one : ActsOnE f 1 1 := by
  intro x hx hx'
  have : (⟨1 * x * 1⁻¹, hx'⟩ : ↥E) = ⟨x, hx⟩ := Subtype.ext (by simp)
  rw [this]
  simp

theorem ActsOnE.pi : ActsOnE f 1 (allOnes 6) := by
  intro x hx hx'
  have : (⟨1 * x * 1⁻¹, hx'⟩ : ↥E) = ⟨x, hx⟩ := Subtype.ext (by simp)
  rw [this, allOnes_comm (f ⟨x, hx⟩)]
  group

theorem ActsOnE.mul (hEn : ∀ g ∈ Subgroup.centralizer ({e} : Set G), ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    {h h' : G} {w w' : Wr 6} (hh' : h' ∈ Subgroup.centralizer ({e} : Set G))
    (a : ActsOnE f h w) (b : ActsOnE f h' w') : ActsOnE f (h * h') (w * w') := by
  intro x hx hx'
  have hy : h' * x * h'⁻¹ ∈ E := hEn h' hh' x hx
  have hy' : h * (h' * x * h'⁻¹) * h⁻¹ ∈ E := by
    rw [show h * (h' * x * h'⁻¹) * h⁻¹ = h * h' * x * (h * h')⁻¹ by group]
    exact hx'
  have h1 := a (h' * x * h'⁻¹) hy hy'
  have h2 := b x hx hy
  have h3 : (⟨h * h' * x * (h * h')⁻¹, hx'⟩ : ↥E) = ⟨h * (h' * x * h'⁻¹) * h⁻¹, hy'⟩ :=
    Subtype.ext (by group)
  rw [h3, h1, h2]
  group

theorem ActsOnE.inv {h : G} {w : Wr 6} (a : ActsOnE f h w) : ActsOnE f h⁻¹ w⁻¹ := by
  intro x hx hx'
  have hy : h * (h⁻¹ * x * h⁻¹⁻¹) * h⁻¹ ∈ E := by
    rw [show h * (h⁻¹ * x * h⁻¹⁻¹) * h⁻¹ = x by group]
    exact hx
  have h1 := a (h⁻¹ * x * h⁻¹⁻¹) hx' hy
  have h2 : (⟨h * (h⁻¹ * x * h⁻¹⁻¹) * h⁻¹, hy⟩ : ↥E) = ⟨x, hx⟩ := Subtype.ext (by group)
  rw [h2] at h1
  calc f ⟨h⁻¹ * x * h⁻¹⁻¹, hx'⟩
      = w⁻¹ * (w * f ⟨h⁻¹ * x * h⁻¹⁻¹, hx'⟩ * w⁻¹) * w := by group
    _ = w⁻¹ * f ⟨x, hx⟩ * w⁻¹⁻¹ := by rw [← h1, inv_inv]

theorem ActsOnE.conj (hEn : ∀ g ∈ Subgroup.centralizer ({e} : Set G), ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    {h a : G} {w v : Wr 6} (hh : h ∈ Subgroup.centralizer ({e} : Set G))
    (ha : a ∈ Subgroup.centralizer ({e} : Set G)) (A : ActsOnE f h w) (B : ActsOnE f a v) :
    ActsOnE f (h * a * h⁻¹) (w * v * w⁻¹) :=
  ActsOnE.mul hEn (Subgroup.inv_mem _ hh) (ActsOnE.mul hEn ha A B) A.inv

theorem ActsOnE.unique (hr : f.range = aeSub 6) {h : G} {w w' : Wr 6}
    (hh : ∀ x ∈ E, h * x * h⁻¹ ∈ E) (a : ActsOnE f h w) (b : ActsOnE f h w') :
    w⁻¹ * w' ∈ piSub 6 := by
  apply mem_piSub_of_centralizes
  intro y hy
  rw [← hr] at hy
  obtain ⟨⟨x, hx⟩, rfl⟩ := hy
  have h1 := a x hx (hh x hx)
  have h2 := b x hx (hh x hx)
  have h3 : (w⁻¹ * w') * f ⟨x, hx⟩ * (w⁻¹ * w')⁻¹ = f ⟨x, hx⟩ := by
    calc (w⁻¹ * w') * f ⟨x, hx⟩ * (w⁻¹ * w')⁻¹
        = w⁻¹ * (w' * f ⟨x, hx⟩ * w'⁻¹) * w := by group
      _ = w⁻¹ * (w * f ⟨x, hx⟩ * w⁻¹) * w := by rw [← h2, h1]
      _ = f ⟨x, hx⟩ := by group
  calc (w⁻¹ * w') * f ⟨x, hx⟩ = ((w⁻¹ * w') * f ⟨x, hx⟩ * (w⁻¹ * w')⁻¹) * (w⁻¹ * w') := by group
    _ = f ⟨x, hx⟩ * (w⁻¹ * w') := by rw [h3]

end Acts

theorem card_piSub : Nat.card (piSub 6) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : piSub 6 = Subgroup.zpowers (allOnes 6) := by
    apply le_antisymm
    · rintro a (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · exact Subgroup.zpowers_le.mpr (Or.inr rfl)
  have h2 : allOnes 6 ≠ (1 : Wr 6) := by decide +kernel
  rw [h1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact allOnes_mul_self 6) h2]

section Graph

variable {G : Type} [Group G] [Finite G] {e : G} {E : Subgroup G} {f : ↥E →* Wr 6}

structure KappaHyp (e : G) (E : Subgroup G) (f : ↥E →* Wr 6) : Prop where
  normal : ∀ g ∈ Subgroup.centralizer ({e} : Set G), ∀ x ∈ E, g * x * g⁻¹ ∈ E
  inj : Function.Injective f
  range : f.range = aeSub 6
  kappa : ∀ h ∈ Subgroup.centralizer ({e} : Set G), ∃ w : Wr 6, ActsOnE f h w
  he2 : e * e = 1
  he1 : e ≠ 1
  e_mem : e ∈ E
  centE : Subgroup.centralizer (E : Set G) = Subgroup.zpowers e

def actionGraph (H : KappaHyp e E f) : Subgroup (G × Wr 6) where
  carrier := {p | p.1 ∈ Subgroup.centralizer ({e} : Set G) ∧ ActsOnE f p.1 p.2}
  mul_mem' := fun {a b} ha hb =>
    ⟨Subgroup.mul_mem _ ha.1 hb.1, ActsOnE.mul H.normal hb.1 ha.2 hb.2⟩
  one_mem' := ⟨Subgroup.one_mem _, ActsOnE.one⟩
  inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, ha.2.inv⟩

theorem KappaHyp.mem_zpowers_of_acts (H : KappaHyp e E f) {g : G}
    (hgC : g ∈ Subgroup.centralizer ({e} : Set G)) (hg : ActsOnE f g 1) :
    g ∈ Subgroup.zpowers e := by
  rw [← H.centE, Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' := H.normal g hgC x hx
  have h1 := hg x hx hx'
  rw [one_mul, inv_one, mul_one] at h1
  have h3 : g * x * g⁻¹ = x := congrArg Subtype.val (H.inj h1)
  calc x * g = (g * x * g⁻¹) * g := by rw [h3]
    _ = g * x := by group

theorem KappaHyp.acts_one_of_mem_zpowers (H : KappaHyp e E f) {g : G}
    (hg : g ∈ Subgroup.zpowers e) : ActsOnE f g 1 := by
  have hgE : g ∈ Subgroup.centralizer (E : Set G) := H.centE ▸ hg
  intro x hx hx'
  have h1 : g * x * g⁻¹ = x := by
    have := Subgroup.mem_centralizer_iff.mp hgE x hx
    calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [this]
      _ = x := by group
  have h2 : (⟨g * x * g⁻¹, hx'⟩ : ↥E) = ⟨x, hx⟩ := Subtype.ext h1
  rw [h2]
  group

theorem KappaHyp.zpowers_le (H : KappaHyp e E f) :
    Subgroup.zpowers e ≤ Subgroup.centralizer ({e} : Set G) := by
  rw [Subgroup.zpowers_le]
  exact Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]

theorem KappaHyp.card_zpowers (H : KappaHyp e E f) : Nat.card (Subgroup.zpowers e) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact H.he2) H.he1]

theorem card_eq_card_wset (H : KappaHyp e E f) {K : Subgroup G}
    (hKH : K ≤ Subgroup.centralizer ({e} : Set G)) (heK : e ∈ K) :
    Nat.card K = Nat.card ((actionGraph H ⊓ K.prod ⊤).map (MonoidHom.snd G (Wr 6))) := by
  set Γ : Subgroup (G × Wr 6) := actionGraph H ⊓ K.prod ⊤ with hΓ
  let p : ↥Γ →* G := (MonoidHom.fst G (Wr 6)).comp Γ.subtype
  let q : ↥Γ →* Wr 6 := (MonoidHom.snd G (Wr 6)).comp Γ.subtype
  have hmem : ∀ x : G × Wr 6, x ∈ Γ ↔
      (x.1 ∈ Subgroup.centralizer ({e} : Set G) ∧ ActsOnE f x.1 x.2) ∧ x.1 ∈ K := by
    intro x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (Subgroup.mem_prod.mp h2).1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Subgroup.mem_prod.mpr ⟨h2, Subgroup.mem_top _⟩⟩
  have hmap : Γ.map (MonoidHom.snd G (Wr 6)) = q.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap]
  have hp_range : p.range = K := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ((hmem _).mp x.2).2
    · intro hg
      obtain ⟨w, hw⟩ := H.kappa g (hKH hg)
      exact ⟨⟨(g, w), (hmem _).mpr ⟨⟨hKH hg, hw⟩, hg⟩⟩, rfl⟩
  have hker : ∀ x : ↥p.ker, ((x : ↥Γ) : G × Wr 6).2 ∈ piSub 6 := by
    intro x
    have h1 : ((x : ↥Γ) : G × Wr 6).1 = 1 := x.2
    obtain ⟨⟨-, hact⟩, -⟩ := (hmem _).mp (x : ↥Γ).2
    rw [h1] at hact
    have := ActsOnE.unique H.range (fun x hx => by simpa using hx) ActsOnE.one hact
    simpa using this
  have hp_ker : Nat.card p.ker = 2 := by
    rw [← card_piSub]
    refine Nat.card_eq_of_bijective (fun x => ⟨((x : ↥Γ) : G × Wr 6).2, hker x⟩) ⟨?_, ?_⟩
    · intro x y hxy
      have h2 : ((x : ↥Γ) : G × Wr 6).2 = ((y : ↥Γ) : G × Wr 6).2 := congrArg Subtype.val hxy
      have h1x : ((x : ↥Γ) : G × Wr 6).1 = 1 := x.2
      have h1y : ((y : ↥Γ) : G × Wr 6).1 = 1 := y.2
      exact Subtype.ext (Subtype.ext (Prod.ext (by rw [h1x, h1y]) h2))
    · intro w
      have hact : ActsOnE f 1 w.1 := by
        rcases w.2 with h | h
        · rw [h]; exact ActsOnE.one
        · rw [h]; exact ActsOnE.pi
      exact ⟨⟨⟨(1, w.1), (hmem _).mpr ⟨⟨Subgroup.one_mem _, hact⟩, K.one_mem⟩⟩, rfl⟩, rfl⟩
  have hker2 : ∀ x : ↥q.ker, ((x : ↥Γ) : G × Wr 6).1 ∈ Subgroup.zpowers e := by
    intro x
    have h1 : ((x : ↥Γ) : G × Wr 6).2 = 1 := x.2
    obtain ⟨⟨hC, hact⟩, -⟩ := (hmem _).mp (x : ↥Γ).2
    rw [h1] at hact
    exact H.mem_zpowers_of_acts hC hact
  have hq_ker : Nat.card q.ker = 2 := by
    rw [← H.card_zpowers]
    refine Nat.card_eq_of_bijective (fun x => ⟨((x : ↥Γ) : G × Wr 6).1, hker2 x⟩) ⟨?_, ?_⟩
    · intro x y hxy
      have h2 : ((x : ↥Γ) : G × Wr 6).1 = ((y : ↥Γ) : G × Wr 6).1 := congrArg Subtype.val hxy
      have h1x : ((x : ↥Γ) : G × Wr 6).2 = 1 := x.2
      have h1y : ((y : ↥Γ) : G × Wr 6).2 = 1 := y.2
      exact Subtype.ext (Subtype.ext (Prod.ext h2 (by rw [h1x, h1y])))
    · intro g
      exact ⟨⟨⟨(g.1, 1), (hmem _).mpr ⟨⟨H.zpowers_le g.2, H.acts_one_of_mem_zpowers g.2⟩,
        Subgroup.zpowers_le.mpr heK g.2⟩⟩, rfl⟩, rfl⟩
  have h1 := Subgroup.card_ker_mul_card_range p
  have h2 := Subgroup.card_ker_mul_card_range q
  rw [hp_ker, hp_range] at h1
  rw [hq_ker] at h2
  omega

theorem KappaHyp.card_centralizer_dvd (H : KappaHyp e E f) :
    Nat.card (Subgroup.centralizer ({e} : Set G)) ∣ 46080 := by
  have h := card_eq_card_wset H (K := Subgroup.centralizer ({e} : Set G)) le_rfl
    (Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh])
  rw [h, ← card_Wr_six]
  exact Subgroup.card_subgroup_dvd_card _

theorem KappaHyp.card_le_of_isPGroup (H : KappaHyp e E f)
    (hS : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G))
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 1024 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hS
  obtain ⟨S', hQS'⟩ := hQ.exists_le_sylow
  have h1 : Nat.card Q ∣ Nat.card S' := Subgroup.card_dvd_of_le hQS'
  have h2 : Nat.card S' = Nat.card S := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h3 : Nat.card S ∣ Nat.card (Subgroup.centralizer ({e} : Set G)) :=
    Subgroup.card_dvd_of_le hS
  have h5 : Nat.card Q ∣ 46080 := h1.trans (h2 ▸ h3.trans H.card_centralizer_dvd)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  rw [hk] at h5 ⊢
  have h6 : 2 ^ k ∣ 1024 * 45 := by simpa using h5
  have h7 : 2 ^ k ∣ 1024 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 45)).dvd_of_dvd_mul_right h6
  exact Nat.le_of_dvd (by norm_num) h7

end Graph

section Sylow

open scoped Pointwise

theorem exists_conj_A64 {P At : Subgroup (Wr 6)} (hPW : P ≤ Wsub) (hP : Nat.card P = 512)
    (hAtP : At ≤ P) (hAt : IsE64 At) (hu : ∀ A' : Subgroup (Wr 6), A' ≤ P → IsE64 A' → A' = At) :
    ∃ g : Wr 6, ∀ x : Wr 6, x ∈ At ↔ g⁻¹ * x * g ∈ A64 := by
  classical
  set P' : Subgroup ↥Wsub := P.subgroupOf Wsub with hP'
  set A' : Subgroup ↥Wsub := A64.subgroupOf Wsub with hA'
  have hcardP' : Nat.card P' = 512 := by
    rw [hP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPW).toEquiv, hP]
  have hcardA' : Nat.card A' = 64 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe A64_le_Wsub).toEquiv, card_A64]
  have hidx : ∀ K : Subgroup ↥Wsub, Nat.card K = 512 → ¬ 2 ∣ K.index := by
    intro K hK h2
    have h := Subgroup.card_mul_index K
    rw [hK, card_Wsub] at h
    omega
  have hP'2 : IsPGroup 2 P' := IsPGroup.of_card (n := 9) (by rw [hcardP']; norm_num)
  have hA'2 : IsPGroup 2 A' := IsPGroup.of_card (n := 6) (by rw [hcardA']; norm_num)
  obtain ⟨Q, hQ⟩ := hA'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Wsub Q (hP'2.toSylow (hidx _ hcardP'))
  have hPeq : P' = MulAut.conj g • (Q : Subgroup ↥Wsub) := by
    have := congrArg (fun R : Sylow 2 ↥Wsub => (R : Subgroup ↥Wsub)) hg
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this.symm
  have hconj : ∀ y : ↥Wsub, y ∈ P' ↔ ∃ s ∈ (Q : Subgroup ↥Wsub), g * s * g⁻¹ = y := by
    intro y
    rw [hPeq, Subgroup.mem_smul_pointwise_iff_exists]
    simp only [MulAut.smul_def, MulAut.conj_apply]
  have hle : A64.map (MulAut.conj (g : Wr 6)).toMonoidHom ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : (⟨a, A64_le_Wsub ha⟩ : ↥Wsub) ∈ Q := hQ (Subgroup.mem_subgroupOf.mpr ha)
    have h2 := (hconj (g * ⟨a, A64_le_Wsub ha⟩ * g⁻¹)).mpr ⟨_, h1, rfl⟩
    exact Subgroup.mem_subgroupOf.mp h2
  have hE64 : IsE64 (A64.map (MulAut.conj (g : Wr 6)).toMonoidHom) :=
    isE64_map_of_injective (MulAut.conj (g : Wr 6)).injective ⟨A64_comm, A64_sq, card_A64⟩
  have heq := hu _ hle hE64
  refine ⟨(g : Wr 6), fun x => ?_⟩
  rw [← heq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : (g : Wr 6)⁻¹ * ((MulAut.conj (g : Wr 6)).toMonoidHom a) * (g : Wr 6) = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [this]
  · intro hx
    refine ⟨_, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end Sylow

section Psi

variable {G : Type} [Group G] [Finite G] {e : G}

structure E64Pair (B T A : Subgroup G) (e : G) : Prop where
  T_le : T ≤ B
  card_T : Nat.card T = 512
  A_le : A ≤ T
  e64 : IsE64 A
  uniq : ∀ A' : Subgroup G, A' ≤ T → IsE64 A' → A' = A
  e_mem : e ∈ A

theorem atilde_facts {B T A : Subgroup G} (Ψ : ↥B →* Wr 6) (hΨ : Function.Injective Ψ)
    (hΨW : ∀ b : ↥B, Ψ b ∈ Wsub) (P : E64Pair B T A e)
    (hΨe : Ψ ⟨e, P.T_le (P.A_le P.e_mem)⟩ = allOnes 6) :
    allOnes 6 ∈ (A.subgroupOf B).map Ψ ∧
      (∀ w : Wr 6, (∀ a ∈ (A.subgroupOf B).map Ψ, w * a * w⁻¹ * a⁻¹ ∈ piSub 6) →
        w ∈ (A.subgroupOf B).map Ψ) ∧
      Nat.card (Subgroup.normalizer (((A.subgroupOf B).map Ψ : Subgroup (Wr 6)) : Set (Wr 6))) ≤
        3072 := by
  have heB : e ∈ B := P.T_le (P.A_le P.e_mem)
  have hAB : A ≤ B := P.A_le.trans P.T_le
  set At : Subgroup (Wr 6) := (A.subgroupOf B).map Ψ with hAt
  set Pt : Subgroup (Wr 6) := (T.subgroupOf B).map Ψ with hPt
  have hPtW : Pt ≤ Wsub := by
    rintro _ ⟨b, -, rfl⟩
    exact hΨW b
  have hcardPt : Nat.card Pt = 512 := by
    rw [hPt, Subgroup.card_map_of_injective hΨ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe P.T_le).toEquiv, P.card_T]
  have hAtPt : At ≤ Pt := Subgroup.map_mono fun b hb => P.A_le hb
  have hE64A : IsE64 (A.subgroupOf B) :=
    isE64_comap_of_injective B.subtype_injective P.e64
      (by rw [Subgroup.range_subtype]; exact hAB)
  have hAtE : IsE64 At := isE64_map_of_injective hΨ hE64A
  have huniq : ∀ A' : Subgroup (Wr 6), A' ≤ Pt → IsE64 A' → A' = At := by
    intro A' hA'Pt hA'
    have hA'r : A' ≤ Ψ.range := hA'Pt.trans (by rintro _ ⟨b, -, rfl⟩; exact ⟨b, rfl⟩)
    have h1 : A'.comap Ψ ≤ T.subgroupOf B := by
      intro b hb
      obtain ⟨b', hb', hbb'⟩ := hA'Pt (Subgroup.mem_comap.mp hb)
      rw [← hΨ hbb']
      exact hb'
    have h2 : IsE64 (A'.comap Ψ) := isE64_comap_of_injective hΨ hA' hA'r
    have h3 : IsE64 ((A'.comap Ψ).map B.subtype) := isE64_map_of_injective B.subtype_injective h2
    have h4 : (A'.comap Ψ).map B.subtype ≤ T := by
      rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h1 hb)
    have h5 := P.uniq _ h4 h3
    have h6 : A'.comap Ψ = A.subgroupOf B := by
      rw [← Subgroup.comap_map_eq_self_of_injective B.subtype_injective (A'.comap Ψ), h5]
      rfl
    rw [← Subgroup.map_comap_eq_self hA'r, h6]
  obtain ⟨g, hg⟩ := exists_conj_A64 hPtW hcardPt hAtPt hAtE huniq
  refine ⟨⟨⟨e, heB⟩, Subgroup.mem_subgroupOf.mpr P.e_mem, hΨe⟩, ?_, ?_⟩
  · intro w hw
    rw [hg]
    apply mem_A64_of_comm_mod_pi
    intro a ha
    have h0 : g⁻¹ * (g * a * g⁻¹) * g ∈ A64 := by
      rw [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
      exact ha
    have h1 : g * a * g⁻¹ ∈ At := (hg _).mpr h0
    have h2 := hw _ h1
    have h3 := (piSub_normal (n := 6)).conj_mem _ h2 g⁻¹
    convert h3 using 1
    group
  · have hnorm : ∀ n : Wr 6, n ∈ Subgroup.normalizer ((At : Subgroup (Wr 6)) : Set (Wr 6)) →
        g⁻¹ * n * g ∈ Subgroup.normalizer ((A64 : Subgroup (Wr 6)) : Set (Wr 6)) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro a
      have hn' := Subgroup.mem_normalizer_iff.mp hn (g * a * g⁻¹)
      constructor
      · intro ha
        have h0 : g⁻¹ * (g * a * g⁻¹) * g ∈ A64 := by
          rw [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
          exact ha
        have h1 := hn'.mp ((hg _).mpr h0)
        have h2 := (hg _).mp h1
        convert h2 using 1
        group
      · intro ha
        have h1 : n * (g * a * g⁻¹) * n⁻¹ ∈ At := by
          rw [hg]
          convert ha using 1
          group
        have h3 := (hg _).mp (hn'.mpr h1)
        rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group] at h3
    refine le_trans (Nat.card_le_card_of_injective
      (fun n : ↥(Subgroup.normalizer ((At : Subgroup (Wr 6)) : Set (Wr 6))) =>
        (⟨g⁻¹ * (n : Wr 6) * g, hnorm n n.2⟩ :
          ↥(Subgroup.normalizer ((A64 : Subgroup (Wr 6)) : Set (Wr 6))))) ?_)
      card_normalizer_A64_le
    intro n m hnm
    have : g⁻¹ * (n : Wr 6) * g = g⁻¹ * (m : Wr 6) * g := congrArg Subtype.val hnm
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))

end Psi

section Final

variable {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G} {f : ↥E →* Wr 6} {Θ : ↥Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat}

theorem E64Pair.of_theta {B T A : Subgroup G} (hTB : T ≤ B) (hT : Nat.card T = 512)
    (hAT : A ≤ T) (hA : IsE64 A) (hAuniq : ∀ A' : Subgroup G, A' ≤ T → IsE64 A' → A' = A)
    (θ : ↥T ≃* ↥S0) (heT : e ∈ T) (hθe : θ ⟨e, heT⟩ = ⟨alpha, alpha_mem_S0⟩)
    (hAθ : ∀ (a : G) (ha : a ∈ T), a ∈ A ↔ ((θ ⟨a, ha⟩ : ↥S0) : StatedSp 3 (ZMod 2)) ∈ A0) :
    E64Pair B T A e :=
  { T_le := hTB, card_T := hT, A_le := hAT, e64 := hA, uniq := hAuniq,
    e_mem := (hAθ e heT).mpr (by rw [hθe]; exact alpha_mem_A0) }

theorem I1Action.normal_of_centralizer (D : I1Action z e E B f Θ φ) :
    ∀ g ∈ Subgroup.centralizer ({e} : Set G), ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
  intro g hg x hx
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  rw [D.E_normal g hg] at h1
  exact h1

theorem I1Action.oddCoreIn_eq_bot (D : I1Action z e E B f Θ φ)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥) : oddCoreIn E = ⊥ := by
  have hEC : E ≤ Subgroup.centralizer ({e} : Set G) := D.E_le_B.trans D.B_le
  have hCN : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (E : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact D.normal_of_centralizer g hg y
    · intro hy
      have := D.normal_of_centralizer g⁻¹ (Subgroup.inv_mem _ hg) _ hy
      simpa [mul_assoc] using this
  have hsub : IsSubnormal E (Subgroup.centralizer ({e} : Set G)) :=
    isSubnormal_of_normal_subgroupOf hEC ((Subgroup.normal_subgroupOf_iff_le_normalizer hEC).mpr hCN)
  have h1 := oddCoreIn_le_of_isSubnormal hsub
  rw [hodd] at h1
  exact le_bot_iff.mp h1

theorem I1Action.kappaHyp (D : I1Action z e E B f Θ φ)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hCE : Subgroup.centralizer (E : Set G) = Subgroup.zpowers e) : KappaHyp e E f := by
  have hO := D.oddCoreIn_eq_bot hodd
  refine ⟨D.normal_of_centralizer, ?_, D.f_range, D.kappa, he2, he1, D.e_mem, hCE⟩
  have : f.ker = ⊥ := by
    rw [D.f_ker, hO]
    exact Subgroup.bot_subgroupOf _
  exact (MonoidHom.ker_eq_bot_iff f).mp this

theorem I1Action.exists_psi (D : I1Action z e E B f Θ φ) (hO : oddCoreIn E = ⊥) :
    ∃ Ψ : ↥B →* Wr 6, Function.Injective Ψ ∧ (∀ b : ↥B, Ψ b ∈ Wsub) ∧
      Ψ ⟨e, D.E_le_B D.e_mem⟩ = allOnes 6 ∧
      ∀ (b : G) (hb : b ∈ B), ActsOnE f b (Ψ ⟨b, hb⟩) := by
  let Ψ : ↥B →* Wr 6 := Wsub.subtype.comp (Θ.symm.toMonoidHom.comp φ)
  have hΨ : ∀ b : ↥B, Ψ b = ((Θ.symm (φ b) : ↥Wsub) : Wr 6) := fun b => rfl
  refine ⟨Ψ, ?_, fun b => (Θ.symm (φ b)).2, ?_, ?_⟩
  · have hker : φ.ker = ⊥ := by
      rw [D.φ_ker, hO]
      exact Subgroup.bot_subgroupOf _
    have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
    intro b b' hbb'
    rw [hΨ, hΨ] at hbb'
    exact hφinj (Θ.symm.injective (Subtype.ext hbb'))
  · rw [hΨ, D.φ_e]
    have : Θ.symm ⟨alpha, alpha_mem_Hhat⟩ = ⟨allOnes 6, allOnes_mem_Wsub⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact D.Θ_pi.symm
    rw [this]
  · intro b hb x hx hx'
    have e1 : φ ⟨b * x * b⁻¹, D.E_le_B hx'⟩ =
        φ ⟨b, hb⟩ * φ ⟨x, D.E_le_B hx⟩ * (φ ⟨b, hb⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    obtain ⟨hm, h1⟩ := D.φ_f x hx
    obtain ⟨hm', h2⟩ := D.φ_f _ hx'
    rw [h1, h2] at e1
    have e2 := congrArg Θ.symm e1
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at e2
    exact congrArg Subtype.val e2

theorem I1Action.centralizer_eq (D : I1Action z e E B f Θ φ)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hCE : Subgroup.centralizer (E : Set G) = Subgroup.zpowers e) {T A : Subgroup G}
    (P : E64Pair B T A e) : Subgroup.centralizer (A : Set G) = A := by
  have H := D.kappaHyp hodd he2 he1 hCE
  obtain ⟨Ψ, hΨinj, hΨW, hΨe, hΨact⟩ := D.exists_psi (D.oddCoreIn_eq_bot hodd)
  obtain ⟨-, hF14a, -⟩ := atilde_facts Ψ hΨinj hΨW P hΨe
  have hAB : A ≤ B := P.A_le.trans P.T_le
  have hAC : ∀ a ∈ A, a ∈ Subgroup.centralizer ({e} : Set G) := fun a ha => D.B_le (hAB ha)
  apply le_antisymm
  · intro h hh
    have hhC : h ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hh e P.e_mem).symm
    obtain ⟨w, hw⟩ := H.kappa h hhC
    have hcomm : ∀ a ∈ (A.subgroupOf B).map Ψ, w * a * w⁻¹ * a⁻¹ ∈ piSub 6 := by
      rintro _ ⟨⟨a, haB⟩, haA, rfl⟩
      have haA' : a ∈ A := Subgroup.mem_subgroupOf.mp haA
      have haC := hAC a haA'
      have h1 := ActsOnE.conj H.normal hhC haC hw (hΨact a haB)
      have hh' : h * a * h⁻¹ = a := by
        have := Subgroup.mem_centralizer_iff.mp hh a haA'
        calc h * a * h⁻¹ = (a * h) * h⁻¹ := by rw [this]
          _ = a := by group
      rw [hh'] at h1
      have h2 := ActsOnE.unique H.range (H.normal a haC) (hΨact a haB) h1
      have h3 := (piSub_normal (n := 6)).conj_mem _ h2 (Ψ ⟨a, haB⟩)
      convert h3 using 1
      group
    obtain ⟨⟨a₀, ha₀B⟩, ha₀A, hwa₀⟩ := hF14a w hcomm
    have ha₀A' : a₀ ∈ A := Subgroup.mem_subgroupOf.mp ha₀A
    have h4 : ActsOnE f (a₀⁻¹ * h) ((Ψ ⟨a₀, ha₀B⟩)⁻¹ * w) :=
      ActsOnE.mul H.normal hhC (hΨact a₀ ha₀B).inv hw
    rw [← hwa₀, inv_mul_cancel] at h4
    have h5 : a₀⁻¹ * h ∈ Subgroup.zpowers e :=
      H.mem_zpowers_of_acts (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAC a₀ ha₀A')) hhC) h4
    have h6 : a₀⁻¹ * h ∈ A := (Subgroup.zpowers_le.mpr P.e_mem) h5
    have h7 : h = a₀ * (a₀⁻¹ * h) := by group
    rw [h7]
    exact Subgroup.mul_mem _ ha₀A' h6
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact P.e64.1 b hb a ha

theorem I1Action.card_normalizer_inf_centralizer_le (D : I1Action z e E B f Θ φ)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hCE : Subgroup.centralizer (E : Set G) = Subgroup.zpowers e) {T A : Subgroup G}
    (P : E64Pair B T A e) :
    Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) ≤
      48 * Nat.card ↥A := by
  have H := D.kappaHyp hodd he2 he1 hCE
  obtain ⟨Ψ, hΨinj, hΨW, hΨe, hΨact⟩ := D.exists_psi (D.oddCoreIn_eq_bot hodd)
  obtain ⟨hπ, -, hN⟩ := atilde_facts Ψ hΨinj hΨW P hΨe
  have hAB : A ≤ B := P.A_le.trans P.T_le
  have hAC : ∀ a ∈ A, a ∈ Subgroup.centralizer ({e} : Set G) := fun a ha => D.B_le (hAB ha)
  have hcardA : Nat.card A = 64 := P.e64.2.2
  set K : Subgroup G := Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)
    with hK
  have heK : e ∈ K :=
    ⟨Subgroup.le_normalizer P.e_mem,
      Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]⟩
  have hKH : K ≤ Subgroup.centralizer ({e} : Set G) := inf_le_right
  have hpi : ∀ c ∈ piSub 6, c ∈ (A.subgroupOf B).map Ψ := by
    rintro c (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact hπ
  have hconj : ∀ (h : G) (w : Wr 6), h ∈ K → ActsOnE f h w →
      ∀ a ∈ (A.subgroupOf B).map Ψ, w * a * w⁻¹ ∈ (A.subgroupOf B).map Ψ := by
    intro h w hhK hw
    rintro _ ⟨⟨a, haB⟩, haA, rfl⟩
    have haA' : a ∈ A := Subgroup.mem_subgroupOf.mp haA
    have hhC := hKH hhK
    have haC := hAC a haA'
    have h1 := ActsOnE.conj H.normal hhC haC hw (hΨact a haB)
    have ha2 : h * a * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hhK.1 a).mp haA'
    have ha2B : h * a * h⁻¹ ∈ B := hAB ha2
    have h2 := ActsOnE.unique H.range (H.normal _ (hAC _ ha2)) (hΨact _ ha2B) h1
    have h3 : Ψ ⟨h * a * h⁻¹, ha2B⟩ ∈ (A.subgroupOf B).map Ψ :=
      ⟨⟨h * a * h⁻¹, ha2B⟩, Subgroup.mem_subgroupOf.mpr ha2, rfl⟩
    have h4 := Subgroup.mul_mem _ h3 (hpi _ h2)
    convert h4 using 1
    group
  have hsub : (actionGraph H ⊓ K.prod ⊤).map (MonoidHom.snd G (Wr 6)) ≤
      Subgroup.normalizer (((A.subgroupOf B).map Ψ : Subgroup (Wr 6)) : Set (Wr 6)) := by
    rintro _ ⟨⟨h, w⟩, ⟨⟨hhC, hw⟩, hhK⟩, rfl⟩
    show w ∈ Subgroup.normalizer (((A.subgroupOf B).map Ψ : Subgroup (Wr 6)) : Set (Wr 6))
    have hhK' : h ∈ K := (Subgroup.mem_prod.mp hhK).1
    have hhK2 : h⁻¹ ∈ K := Subgroup.inv_mem _ hhK'
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hconj h w hhK' hw a ha
    · intro ha
      have := hconj h⁻¹ w⁻¹ hhK2 hw.inv _ ha
      convert this using 1
      group
  rw [card_eq_card_wset H hKH heK, hcardA]
  exact (Subgroup.card_le_of_le hsub).trans hN

theorem I1Action.card_le_of_isPGroup (D : I1Action z e E B f Θ φ)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hCE : Subgroup.centralizer (E : Set G) = Subgroup.zpowers e)
    (hS : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G))
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 1024 :=
  (D.kappaHyp hodd he2 he1 hCE).card_le_of_isPGroup hS hQ

theorem I1Action.naCount_hyps (D : I1Action z e E B f Θ φ)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hCE : Subgroup.centralizer (E : Set G) = Subgroup.zpowers e)
    (hS : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G))
    {T A : Subgroup G} (P : E64Pair B T A e) :
    Subgroup.centralizer (A : Set G) = A ∧
      Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) ≤
        48 * Nat.card ↥A ∧
      ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.normalizer (A : Set G) →
        Nat.card ↥Q ≤ 1024 :=
  ⟨D.centralizer_eq hodd he2 he1 hCE P, D.card_normalizer_inf_centralizer_le hodd he2 he1 hCE P,
    fun _ hQ _ => D.card_le_of_isPGroup hodd he2 he1 hCE hS hQ⟩

end Final

section Theta

variable
  {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G} {f : ↥E →* Wr 6} {Θ : ↥Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat}

theorem I1Action.exists_theta (D : I1Action z e E B f Θ φ)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥)
    {T : Subgroup G} (hTB : T ≤ B) (hT : Nat.card T = 512) :
    ∃ (A : Subgroup G) (θ : ↥T ≃* ↥S0) (heT : e ∈ T),
      θ ⟨e, heT⟩ = ⟨alpha, alpha_mem_S0⟩ ∧ E64Pair B T A e ∧
      ∀ (a : G) (ha : a ∈ T), a ∈ A ↔ ((θ ⟨a, ha⟩ : ↥S0) : StatedSp 3 (ZMod 2)) ∈ A0 := by
  obtain ⟨h, hmap, θ, hθ, A, hAT, hA, hAθ, -, hAuniq⟩ :=
    exists_conj_of_hat φ D.φ_surj D.φ_ker hTB hT
  have heB : e ∈ B := D.E_le_B D.e_mem
  have hcentral : ∀ y : ↥Hhat,
      y * (⟨alpha, alpha_mem_Hhat⟩ : ↥Hhat) = ⟨alpha, alpha_mem_Hhat⟩ * y := fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Hhat_le_centralizer_alpha y.2))
  have hα : (⟨alpha, alpha_mem_Hhat⟩ : ↥Hhat) ∈ (T.subgroupOf B).map φ := by
    rw [hmap]
    refine ⟨⟨alpha, alpha_mem_Hhat⟩, Subgroup.mem_subgroupOf.mpr alpha_mem_S0, ?_⟩
    show h * ⟨alpha, alpha_mem_Hhat⟩ * h⁻¹ = ⟨alpha, alpha_mem_Hhat⟩
    rw [hcentral h, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨x, hxT, hxφ⟩ := hα
  have hinj : Function.Injective φ := by
    refine (MonoidHom.ker_eq_bot_iff φ).mp ?_
    rw [D.φ_ker, D.oddCoreIn_eq_bot hodd]
    exact Subgroup.bot_subgroupOf _
  have hx : x = ⟨e, heB⟩ := hinj (hxφ.trans D.φ_e.symm)
  have heT : e ∈ T := by
    have h1 : ((x : ↥B) : G) ∈ T := Subgroup.mem_subgroupOf.mp hxT
    rw [hx] at h1
    exact h1
  have hθe : θ ⟨e, heT⟩ = ⟨alpha, alpha_mem_S0⟩ := by
    apply Subtype.ext
    rw [hθ e heT heB, D.φ_e]
    show ((h⁻¹ * ⟨alpha, alpha_mem_Hhat⟩ * h : ↥Hhat) : StatedSp 3 (ZMod 2)) = alpha
    rw [hcentral h⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  exact ⟨A, θ, heT, hθe, E64Pair.of_theta hTB hT hAT hA hAuniq θ heT hθe hAθ, hAθ⟩

end Theta

end CFSG.ClassicalInvolution.Sp62Rec

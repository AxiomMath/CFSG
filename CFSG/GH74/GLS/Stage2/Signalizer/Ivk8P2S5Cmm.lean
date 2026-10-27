module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Xd
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Amb

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_Fs_le (X : Subgroup G) :
    X ⊓ centralizer ((Fs X : Subgroup G) : Set G) ≤ Fs X := by
  intro x hx
  obtain ⟨hxX, hxc⟩ := hx
  have hc : (⟨x, hxX⟩ : X) ∈ centralizer ((generalizedFitting ↥X : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp hxc (y : G) ⟨y, hy, rfl⟩
    exact Subtype.ext this
  exact ⟨⟨x, hxX⟩, CFSG.centralizer_generalizedFitting_le ↥X hc, rfl⟩

theorem Fm_commute_Em' (N : Subgroup G) : ∀ f ∈ Fm N, ∀ e ∈ Em N, e * f = f * e := by
  intro f hf e he
  have h : Fm N ≤ centralizer ((Em N : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (L915.Fm_comm_Em N)
  exact Subgroup.mem_centralizer_iff.1 (h hf) e he

theorem comm_centralizes_Fm {z : G} {M C : Subgroup G} (hMz : M = centralizer {z})
    (hz2 : z * z = 1) (hzC : z ∈ C) (hF1 : Fpi (piF' M) C ⊓ M = ⊥) (hF2 : Fpi (piF M) C ≤ M)
    {c : G} (hc : c ∈ C) : Fm C ≤ centralizer ({⁅c, z⁆} : Set G) := by
  have hσ' : ∀ q ∈ piF' M, q.Prime := fun q hq => prime_of_mem_piF' hq
  have hσ : ∀ q ∈ piF M, q.Prime := fun q hq => prime_of_mem_piF hq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨hinv, -⟩ := inverts_F1 hMz hz2 (Subgroup.le_normalizer hzC) hF1
  refine (Fm_le_Fpi_sup (fun r => r ∣ Nat.card ↥(Fm M)) C).trans (sup_le ?_ ?_)
  · intro f hf
    have hf' : c⁻¹ * f * c ∈ Fpi (piF M) C := by
      have := (Subgroup.mem_normalizer_iff.1
        (Subgroup.inv_mem _ (le_normalizer_Fpi hσ C hc)) f).1 hf
      simpa using this
    have h1 : z * f = f * z :=
      (Subgroup.mem_centralizer_singleton_iff.1 (hMz ▸ hF2 hf : f ∈ centralizer ({z} : Set G))).symm
    have h2 : z * (c⁻¹ * f * c) = (c⁻¹ * f * c) * z :=
      (Subgroup.mem_centralizer_singleton_iff.1
        (hMz ▸ hF2 hf' : c⁻¹ * f * c ∈ centralizer ({z} : Set G))).symm
    have h2' : c * z * (c⁻¹ * f * c) = c * (c⁻¹ * f * c) * z := by
      rw [mul_assoc c z, h2, ← mul_assoc]
    have e1 : z⁻¹ * f = f * z⁻¹ := by
      calc z⁻¹ * f = z⁻¹ * (f * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * f) * z⁻¹ := by rw [h1]
        _ = f * z⁻¹ := by group
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc f * ⁅c, z⁆ = (c * (c⁻¹ * f * c) * z * c⁻¹ * z⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = c * z * (c⁻¹ * f * c) * c⁻¹ * z⁻¹ := by rw [h2']
      _ = c * z * c⁻¹ * (f * z⁻¹) := by group
      _ = c * z * c⁻¹ * (z⁻¹ * f) := by rw [e1]
      _ = ⁅c, z⁆ * f := by simp only [commutatorElement_def]; group

  · intro f hf
    have hf' : c⁻¹ * f * c ∈ Fpi (piF' M) C := by
      have := (Subgroup.mem_normalizer_iff.1
        (Subgroup.inv_mem _ (le_normalizer_Fpi hσ' C hc)) f).1 hf
      simpa using this
    have h1 : z * f * z⁻¹ = f⁻¹ := hinv f hf
    have h2 : z * (c⁻¹ * f * c) * z⁻¹ = (c⁻¹ * f * c)⁻¹ := hinv _ hf'
    have e0 : z⁻¹ * f * z = f⁻¹ := by
      calc z⁻¹ * f * z = z * f * z⁻¹ := by rw [hzi]
        _ = f⁻¹ := h1
    have e1 : z⁻¹ * f = f⁻¹ * z⁻¹ := by
      calc z⁻¹ * f = (z⁻¹ * f * z) * z⁻¹ := by group
        _ = f⁻¹ * z⁻¹ := by rw [e0]
    have e2 : z * (c⁻¹ * f * c)⁻¹ * z⁻¹ = c⁻¹ * f * c := by
      calc z * (c⁻¹ * f * c)⁻¹ * z⁻¹ = (z * (c⁻¹ * f * c) * z⁻¹)⁻¹ := by group
        _ = ((c⁻¹ * f * c)⁻¹)⁻¹ := by rw [h2]
        _ = c⁻¹ * f * c := by group
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc f * ⁅c, z⁆ = (c * (c⁻¹ * f * c) * z * c⁻¹ * z⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = c * (z * (c⁻¹ * f * c)⁻¹ * z⁻¹) * z * c⁻¹ * z⁻¹ := by rw [e2]
      _ = c * z * c⁻¹ * (f⁻¹ * z⁻¹) := by group
      _ = c * z * c⁻¹ * (z⁻¹ * f) := by rw [e1]
      _ = ⁅c, z⁆ * f := by simp only [commutatorElement_def]; group
theorem comm_le_Em_sup_Fm {z : G} {M C : Subgroup G} (hMz : M = centralizer {z})
    (hz2 : z * z = 1) (hzC : z ∈ C) (hF1 : Fpi (piF' M) C ⊓ M = ⊥) (hF2 : Fpi (piF M) C ≤ M)
    (ha : ⁅C, zpowers z⁆ ≤ Em C ⊔ (C ⊓ centralizer ((Em C : Subgroup G) : Set G))) :
    ⁅C, zpowers z⁆ ≤ Em C ⊔ Fm C := by
  have hcent : ⁅C, zpowers z⁆ ≤ centralizer ((Fm C : Subgroup G) : Set G) := by
    refine commutator_zpowers_le_of hz2 fun c hc => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.1
      (comm_centralizes_Fm hMz hz2 hzC hF1 hF2 hc hf)
  intro y hy
  obtain ⟨e, he, c₀, hc₀, rfl⟩ := CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute
    (A := Em C) (B := C ⊓ centralizer ((Em C : Subgroup G) : Set G))
    (fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb.2 a ha) (ha hy)
  have hy' : e * c₀ ∈ centralizer ((Fm C : Subgroup G) : Set G) := hcent hy
  have he' : e ∈ centralizer ((Fm C : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun f hf => (Fm_commute_Em' C f hf e he).symm
  have hc₀F : c₀ ∈ centralizer ((Fm C : Subgroup G) : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ he') hy'
    simpa using this
  have hle : Fm C ⊔ Em C ≤ centralizer ({c₀} : Set G) :=
    sup_le (fun f hf => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hc₀F f hf))
      (fun e' he'' => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hc₀.2 e' he''))
  have hc₀Fs : c₀ ∈ centralizer ((Fs C : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    have hh' : h ∈ Fm C ⊔ Em C := by
      rw [← L915.Fs_eq_sup]
      exact hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh')
  have hc₀' : c₀ ∈ Fm C ⊔ Em C := by
    rw [← L915.Fs_eq_sup]
    exact inf_centralizer_Fs_le C ⟨hc₀.1, hc₀Fs⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (by rwa [sup_comm] at hc₀')

theorem comm2_le_of {z : G} {M C : Subgroup G} (hMz : M = centralizer {z}) (hz2 : z * z = 1)
    (hzC : z ∈ C) (hF1 : Fpi (piF' M) C ⊓ M = ⊥) (hF2 : Fpi (piF M) C ≤ M)
    (ha : ⁅C, zpowers z⁆ ≤ Em C ⊔ (C ⊓ centralizer ((Em C : Subgroup G) : Set G))) :
    ⁅⁅C, zpowers z⁆, zpowers z⁆ ≤ Em C ⊔ Fpi (piF' M) C := by
  have hσ' : ∀ q ∈ piF' M, q.Prime := fun q hq => prime_of_mem_piF' hq
  have hD := comm_le_Em_sup_Fm hMz hz2 hzC hF1 hF2 ha
  set N₀ : Subgroup G := Em C ⊔ Fpi (piF' M) C with hN₀
  have hCN : ∀ g ∈ C, g ∈ normalizer (N₀ : Set G) := fun g hg =>
    mem_normalizer_sup (le_normalizer_Em C hg) (le_normalizer_Fpi hσ' C hg)
  have hcommN : ∀ y ∈ N₀, ⁅y, z⁆ ∈ N₀ := by
    intro y hy
    have e : ⁅y, z⁆ = y * (z * y⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact N₀.mul_mem hy ((Subgroup.mem_normalizer_iff.1 (hCN z hzC) y⁻¹).1 (N₀.inv_mem hy))
  let K : Subgroup G :=
    { carrier := {y | y ∈ C ∧ ⁅y, z⁆ ∈ N₀}
      one_mem' := ⟨C.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haC, ha'⟩ ⟨hbC, hb⟩
        refine ⟨C.mul_mem haC hbC, ?_⟩
        have e : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N₀.mul_mem ((Subgroup.mem_normalizer_iff.1 (hCN a haC) _).1 hb) ha'
      inv_mem' := by
        rintro a ⟨haC, ha'⟩
        refine ⟨C.inv_mem haC, ?_⟩
        have e : ⁅a⁻¹, z⁆ = a⁻¹ * ⁅a, z⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hCN a⁻¹ (C.inv_mem haC)) _).1 (N₀.inv_mem ha') }
  have hN₀C : ∀ y ∈ N₀, y ∈ K := fun y hy =>
    ⟨(sup_le (Em_le C) ((Fpi_le_Fm _ C).trans (Fm_le C))) hy, hcommN y hy⟩
  have hEmK : Em C ≤ K := fun y hy => hN₀C y (Subgroup.mem_sup_left hy)
  have hF1K : Fpi (piF' M) C ≤ K := fun y hy => hN₀C y (Subgroup.mem_sup_right hy)
  have hF2K : Fpi (piF M) C ≤ K := by
    intro f hf
    refine ⟨(Fpi_le_Fm _ C).trans (Fm_le C) hf, ?_⟩
    have hc : Commute f z :=
      Subgroup.mem_centralizer_singleton_iff.1 (hMz ▸ hF2 hf : f ∈ centralizer ({z} : Set G))
    rw [commutatorElement_eq_one_iff_commute.2 hc]
    exact N₀.one_mem
  have hFmK : Fm C ≤ K := (Fm_le_Fpi_sup (fun r => r ∣ Nat.card ↥(Fm M)) C).trans
    (sup_le hF2K hF1K)
  exact commutator_zpowers_le_of hz2 fun y hy => (sup_le hEmK hFmK (hD hy)).2

end Amb

section Wrap

variable {G : Type} [Group G] [Finite G]

theorem comm2_le_XdR (hB12 : Bender12) (h184 : Lemma18_4ac) (h171 : Prop17_1) {z : G}
    {k : Kind} {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G}
    (hctx : Ctx18 G z k S M p E t) {d : G} (hdE : d ∈ E) (hd1 : d ≠ 1)
    (hdM : ¬ centralizer ({d} : Set G) ≤ M) :
    ⁅⁅centralizer ({d} : Set G), zpowers z⁆, zpowers z⁆ ≤ XdR M d := by
  have hF := S5Facts.of_ctx h171 hctx
  obtain ⟨hzC, hVC, hF1, hF2⟩ := centralizer_facts hB12 h171 hctx hdE
  have hCtop : centralizer ({d} : Set G) ≠ ⊤ := centralizer_ne_top hF.hkps hd1
  have hnormC : ∀ v ∈ Vof M E, v ∈ normalizer ((centralizer ({d} : Set G) : Subgroup G) : Set G) :=
    fun v hv => Subgroup.le_normalizer (hVC hv)
  have ha : ⁅centralizer ({d} : Set G), zpowers z⁆ ≤ Em (centralizer ({d} : Set G)) ⊔
      (centralizer ({d} : Set G) ⊓ centralizer ((Em (centralizer ({d} : Set G)) : Subgroup G) :
        Set G)) := by
    by_cases hJ : ∃ J, IsCompIn (centralizer ({d} : Set G)) J
    · obtain ⟨J, hJ⟩ := hJ
      exact (h184 G z k S M p E t hctx _ hnormC hdM hCtop J hJ).1.2
    · have hEm : Em (centralizer ({d} : Set G)) = ⊥ :=
        le_bot_iff.1 (Em_le_of_forall_comp fun J hJ' => absurd hJ' (fun h => hJ ⟨J, h⟩))
      rw [hEm]
      refine (commutator_zpowers_le hzC).trans ?_
      intro x hx
      refine Subgroup.mem_sup_right ⟨hx, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      have : h = 1 := by simpa using hh
      rw [this]
      simp
  exact comm2_le_of hF.hMz (mul_self_eq_one_of_orderOf hF.hz2) hzC hF1 hF2 ha

omit [Finite G] in
theorem odd_inverted_mem_XdR {M : Subgroup G} {d z x : G}
    (hc2 : ⁅⁅centralizer ({d} : Set G), zpowers z⁆, zpowers z⁆ ≤ XdR M d)
    (hx : x ∈ centralizer ({d} : Set G)) (hinv : z * x * z⁻¹ = x⁻¹) (hodd : Odd (orderOf x)) :
    x ∈ XdR M d :=
  hc2 (mem_commutator_of_inverts hinv hodd (mem_commutator_of_inverts hinv hodd hx))

omit [Finite G] in
theorem le_XdR_of_comp {M : Subgroup G} {d z : G} {J : Subgroup G}
    (hc2 : ⁅⁅centralizer ({d} : Set G), zpowers z⁆, zpowers z⁆ ≤ XdR M d)
    (hJC : J ≤ centralizer ({d} : Set G)) (hJz : ⁅J, zpowers z⁆ = J) : J ≤ XdR M d := by
  have h1 : J ≤ ⁅centralizer ({d} : Set G), zpowers z⁆ :=
    hJz ▸ Subgroup.commutator_mono hJC le_rfl
  calc J = ⁅J, zpowers z⁆ := hJz.symm
    _ ≤ ⁅⁅centralizer ({d} : Set G), zpowers z⁆, zpowers z⁆ := Subgroup.commutator_mono h1 le_rfl
    _ ≤ XdR M d := hc2

end Wrap

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

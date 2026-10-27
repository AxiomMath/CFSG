module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Cent
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Fit

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Cent

variable {G : Type} [Group G]

theorem centralizer_ne_top (hkps : IsKProperSimple G) {d : G} (hd : d ≠ 1) :
    centralizer ({d} : Set G) ≠ ⊤ := by
  intro htop
  obtain ⟨hs, ⟨a, b, hab⟩, -⟩ := hkps
  have hc : d ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({d} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h] at hc
    exact hd (Subgroup.mem_bot.1 hc)
  · have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem centralizer_le_normalizer_zpowers (d : G) :
    centralizer ({d} : Set G) ≤ normalizer ((zpowers d : Subgroup G) : Set G) := by
  intro c hc
  have hcd : c * d = d * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  have hcomm : ∀ n : ℤ, c * d ^ n = d ^ n * c := fun n => ((Commute.zpow_right hcd n)).eq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : c * d ^ n * c⁻¹ = d ^ n := by rw [hcomm n]; group
    rw [this]
    exact Subgroup.zpow_mem_zpowers d n
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : x = d ^ n := by
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = c⁻¹ * d ^ n * c := by rw [← hn]
        _ = d ^ n := by
          have h2 : c⁻¹ * d ^ n = d ^ n * c⁻¹ :=
            (Commute.inv_left (Commute.zpow_right hcd n)).eq
          rw [h2]
          group
    rw [this]
    exact Subgroup.zpow_mem_zpowers d n

theorem normalizer_zpowers_le_normalizer_centralizer [Finite G] (d : G) :
    normalizer ((zpowers d : Subgroup G) : Set G) ≤ normalizer ((centralizer ({d} : Set G) :
      Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_of_forall_conj fun c hc => ?_
  have hcd : c * d = d * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  have hcomm : ∀ m : ℤ, c * d ^ m = d ^ m * c := fun m => ((Commute.zpow_right hcd m)).eq
  have h1 : n⁻¹ * d * n ∈ zpowers d := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) d).1 (Subgroup.mem_zpowers d)
    simpa using this
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hdn : d = n * d ^ m * n⁻¹ := by
    rw [hm]
    group
  symm
  calc d * (n * c * n⁻¹) = n * d ^ m * n⁻¹ * (n * c * n⁻¹) := by rw [← hdn]
    _ = n * (d ^ m * c) * n⁻¹ := by group
    _ = n * (c * d ^ m) * n⁻¹ := by rw [hcomm m]
    _ = (n * c * n⁻¹) * (n * d ^ m * n⁻¹) := by group
    _ = (n * c * n⁻¹) * d := by rw [← hdn]

end Cent

section Main

variable {G : Type} [Group G] [Finite G]

theorem centralizer_facts (hB12 : Bender12) (h171 : Prop17_1) {z : G} {k : Kind}
    {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) {d : G}
    (hdE : d ∈ E) :
    z ∈ centralizer ({d} : Set G) ∧ Vof M E ≤ centralizer ({d} : Set G) ∧
      Fpi (piF' M) (centralizer ({d} : Set G)) ⊓ M = ⊥ ∧
      Fpi (piF M) (centralizer ({d} : Set G)) ≤ M := by
  have hF := S5Facts.of_ctx h171 hctx
  have hp : p.Prime := hctx.prime
  have hdFm : d ∈ Fm M := (Op_le_Fm p hp M) (hctx.E_le hdE)
  have hdM' : d ∈ M := Fm_le M hdFm
  have hdz : d * z = z * d :=
    Subgroup.mem_centralizer_singleton_iff.1 (hF.hMz ▸ hdM' : d ∈ centralizer ({z} : Set G))
  have hben := bender_apply hB12 hF.hkps hF.hMc hF.hnq (Y := zpowers d)
    (N := normalizer ((zpowers d : Subgroup G) : Set G)) (Subgroup.zpowers_le.2 hdFm) inf_le_right
  have hCN : centralizer ({d} : Set G) ≤ normalizer ((zpowers d : Subgroup G) : Set G) :=
    centralizer_le_normalizer_zpowers d
  have hNC := normalizer_zpowers_le_normalizer_centralizer d
  have hσ' : ∀ q ∈ piF' M, q.Prime := fun q hq => prime_of_mem_piF' hq
  have hσ : ∀ q ∈ piF M, q.Prime := fun q hq => prime_of_mem_piF hq
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 hdz.symm, ?_, ?_, ?_⟩
  · intro v hv
    have := (Subgroup.mem_centralizer_iff.1 hv.2) d hdE
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  · exact eq_bot_iff.2 ((inf_le_inf_right M (Fpi_le_Fpi_of_normal hσ' hCN hNC)).trans hben.1.le)
  · exact (Fpi_le_Fpi_of_normal hσ hCN hNC).trans hben.2

theorem centralizer_le_normalizer_XdR {M : Subgroup G} (hσ' : ∀ q ∈ piF' M, q.Prime) (d : G) :
    centralizer ({d} : Set G) ≤ normalizer ((XdR M d : Subgroup G) : Set G) := fun _ hg =>
  mem_normalizer_sup (le_normalizer_Em _ hg) (le_normalizer_Fpi hσ' _ hg)

omit [Finite G] in
theorem XdR_le_centralizer (M : Subgroup G) (d : G) : XdR M d ≤ centralizer ({d} : Set G) :=
  sup_le (Em_le _) ((Fpi_le_Fm _ _).trans (Fm_le _))

theorem XdR_mem_XfamR (hB12 : Bender12) (h183 : Lemma18_3a) (h171 : Prop17_1) (hcl : Claim18Xd)
    {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G}
    (hctx : Ctx18 G z k S M p E t) {d : G} (hdE : d ∈ E) (hd1 : d ≠ 1)
    (hdM : ¬ centralizer ({d} : Set G) ≤ M) : XdR M d ∈ XfamR z M (Vof M E) := by
  have hF := S5Facts.of_ctx h171 hctx
  have hz2' : z * z = 1 := mul_self_eq_one_of_orderOf hF.hz2
  obtain ⟨hzC, hVC, hF1, hF2⟩ := centralizer_facts hB12 h171 hctx hdE
  have hCtop : centralizer ({d} : Set G) ≠ ⊤ := centralizer_ne_top hF.hkps hd1
  have hσ' : ∀ q ∈ piF' M, q.Prime := fun q hq => prime_of_mem_piF' hq
  have hσ : ∀ q ∈ piF M, q.Prime := fun q hq => prime_of_mem_piF hq
  have hnormC : ∀ v ∈ Vof M E, v ∈ normalizer ((centralizer ({d} : Set G) : Subgroup G) : Set G) :=
    fun v hv => Subgroup.le_normalizer (hVC hv)
  have hCnormN := centralizer_le_normalizer_XdR (M := M) hσ' d
  have hNC := XdR_le_centralizer M d
  have hzN : z ∈ normalizer ((XdR M d : Subgroup G) : Set G) := hCnormN hzC
  obtain ⟨hinv, hodd⟩ := inverts_F1 hF.hMz hz2' (Subgroup.le_normalizer hzC) hF1
  have hF1N : Fpi (piF' M) (centralizer ({d} : Set G)) ≤ ⁅XdR M d, zpowers z⁆ := fun f hf =>
    mem_commutator_of_inverts (hinv f hf) (hodd f hf)
      ((le_sup_right : Fpi (piF' M) (centralizer ({d} : Set G)) ≤ XdR M d) hf)
  have hEmN : Em (centralizer ({d} : Set G)) ≤ ⁅XdR M d, zpowers z⁆ := by
    refine Em_le_of_forall_comp fun J hJ => ?_
    have hJz : ⁅J, zpowers z⁆ = J :=
      (h183 G z k S M p E t hctx _ hnormC hdM hCtop J hJ).2.1
    calc J = ⁅J, zpowers z⁆ := hJz.symm
      _ ≤ ⁅XdR M d, zpowers z⁆ := Subgroup.commutator_mono
          ((le_Em_of_isCompIn hJ).trans
            (le_sup_left : Em (centralizer ({d} : Set G)) ≤ XdR M d)) le_rfl
  have hle1 : ⁅XdR M d, zpowers z⁆ ≤ XdR M d := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact commutator_zpowers_self_mem hz2' hzN hx n
  have hle2 : XdR M d ≤ ⁅XdR M d, zpowers z⁆ := sup_le hEmN hF1N
  refine ⟨?_, ?_, ?_, le_antisymm hle1 hle2, ?_, ?_⟩
  · intro h
    exact hcl G z k S M p E t hctx d hdE hd1 hdM (by rw [h]; exact bot_le)
  · intro h
    exact hCtop (top_le_iff.1 (h ▸ hNC))
  · intro v hv
    exact hCnormN (hVC hv)
  · exact eq_bot_iff.2 ((inf_le_inf_right M (Fpi_le_Fpi_of_normal hσ' hNC hCnormN)).trans hF1.le)
  · exact (Fpi_le_Fpi_of_normal hσ hNC hCnormN).trans hF2

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

module

public import CFSG.ClassicalInvolution.AschTight.S1916FusStmt
public import CFSG.ClassicalInvolution.AschTight.S1916Tr
public import CFSG.ClassicalInvolution.AschTight.Hall196Idx2
public import CFSG.ClassicalInvolution.AschTight.S1916Sec
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets5

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.GorensteinWalter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

omit [Finite G] in
theorem conjSub_top (c : G) : conjSub c (⊤ : Subgroup G) = ⊤ := by
  ext x
  simp [mem_conjSub_iff]

theorem mem_normalizer_sup_cStar (hd : Sec19Data p f K z S W) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    c ∈ Subgroup.normalizer ((sec19X K z ⊔ centralizerModOdd ⊤ K : Subgroup G) : Set G) := by
  refine mem_normalizer_sup (mem_normalizer_iff_conjSub_eq.mpr (conjSub_sec19X K hc)) ?_
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  exact Hall196.conjSub_centralizerModOdd ((sd_normalizer_eq hd).ge hc) (conjSub_top c)

theorem commutator_mem_sup_cStar [IsSimpleGroup G] (hd : Sec19Data p f K z S W) {c d : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hd' : d ∈ Subgroup.centralizer ({z} : Set G)) :
    c * d * c⁻¹ * d⁻¹ ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  have ht := hd.tight
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD ht
  have hNC := sd_normalizer_eq hd
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hNC.ge hc
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := hNC.ge hd'
  set Ψ := normalizerToPGammaL2Mod e hFcard hF h3 with hΨ
  set c' : Subgroup.normalizer (K : Set G) := ⟨c, hcN⟩
  set d' : Subgroup.normalizer (K : Set G) := ⟨d, hdN⟩
  have hcyc := pGammaL2_quotient_pgl_isCyclic (GaloisField p f) hF
  have hcomm : ∀ x y : PGammaL2 (GaloisField p f) ⧸
      (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range,
      x * y = y * x := fun x y => (IsCyclic.commGroup).mul_comm x y
  have hu : Ψ (c' * d' * c'⁻¹ * d'⁻¹) ∈ pGammaL2PGLRange (GaloisField p f) := by
    have h1 : (QuotientGroup.mk (Ψ (c' * d' * c'⁻¹ * d'⁻¹)) : PGammaL2 (GaloisField p f) ⧸
        (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range)
          = 1 := by
      simp only [map_mul, map_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hcomm (QuotientGroup.mk (Ψ c')) (QuotientGroup.mk (Ψ d'))]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  rw [← Hall196.map_sec19X_eq_pGammaL2PGLRange hd e hFcard hF h3] at hu
  obtain ⟨x, hxX, hx⟩ := hu
  set y := x⁻¹ * (c' * d' * c'⁻¹ * d'⁻¹) with hy
  have hΨy : Ψ y = 1 := by rw [hy, map_mul, map_inv, hx, inv_mul_cancel]
  have hyC : (y : G) ∈ centralizerModOdd ⊤ K := by
    refine ⟨Subgroup.mem_top _, y.2, mem_normalizer_oddCoreOf_of_mem_normalizer y.2, ?_⟩
    exact (Hall196.normalizerToPGammaL2Mod_eq_one_iff e hFcard hF h3 y).mp hΨy
  have e1 : c * d * c⁻¹ * d⁻¹ = (x : G) * (y : G) := by
    rw [hy]
    simp [c', d', mul_assoc]
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hxX))
    (Subgroup.mem_sup_right hyC)

variable (p f) in
theorem c19_16FNe9_of (hInv : C19_16InvTmp p f) (hFus : C19_16FusTmp p f) :
    C19_16FNe9Tmp p f := by
  intro G _ _ _ K z S W hd hq
  by_contra hS
  obtain ⟨a, haS, ha2, haT⟩ := hInv G K z S W hd hq hS
  have hCz := hd.hSz
  refine false_of_transfer hd.tight.branch.nonabelian S
    (P := (S : Subgroup G) ⊓ (sec19X K z ⊔ centralizerModOdd ⊤ K))
    (fun s hs => mem_normalizer_inf (Subgroup.le_normalizer hs)
      (mem_normalizer_sup_cStar hd (hCz hs)))
    (fun x hx y hy => ⟨S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy),
      commutator_mem_sup_cStar hd (hCz hx) (hCz hy)⟩) haS (fun h => haT h.2) ha2 ?_
  intro g hg
  have hgz : (g⁻¹ * a * g) * z = z * (g⁻¹ * a * g) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hCz hg))
  have hzC : g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z * g⁻¹ * a = g * (z * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * z) * g⁻¹ := by rw [hgz]
      _ = a * (g * z * g⁻¹) := by group
  obtain ⟨c, hcC, hcz⟩ := hFus G K z S W hd hq a haS ha2 haT g hzC
  have hca : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  set d := c⁻¹ * g with hd'
  have hdz : d ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc d * z = c⁻¹ * (g * z * g⁻¹) * g := by rw [hd']; group
      _ = c⁻¹ * (c * z * c⁻¹) * g := by rw [hcz]
      _ = z * d := by rw [hd']; group
  have hb : g⁻¹ * a * g = d⁻¹ * a * d := by
    have h1 : c * a * c⁻¹ = a := by rw [hca, mul_inv_cancel_right]
    calc g⁻¹ * a * g = g⁻¹ * (c * a * c⁻¹) * g := by rw [h1]
      _ = d⁻¹ * a * d := by rw [hd']; group
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := hCz haS
  refine ⟨S.mul_mem (S.inv_mem hg) haS, ?_⟩
  have h2 := commutator_mem_sup_cStar hd (Subgroup.inv_mem _ hdz) (Subgroup.inv_mem _ haC)
  have e : (g⁻¹ * a * g)⁻¹ * a = d⁻¹ * a⁻¹ * d⁻¹⁻¹ * a⁻¹⁻¹ := by
    rw [hb]
    group
  rw [e]
  exact h2

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

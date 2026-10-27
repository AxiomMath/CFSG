module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.Core
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.NotSolv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NormalizerTransitive
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.A4V
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

section Reduction

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem isSylowTwoOf_gnImg_top (hGN : GNSetting X T) : IsSylowTwoOf (gnImg T T) ⊤ := by
  have hp : IsPGroup 2 (T.map (QuotientGroup.mk' (gnC T))) := hGN.sylow.2.1.map _
  refine ⟨le_top, hp, ?_⟩
  intro h
  have h' : 2 ∣ (gnImg T T).relIndex ⊤ := h
  rw [Subgroup.relIndex_top_right] at h'
  apply hGN.sylow.2.2
  show 2 ∣ T.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  change 2 ∣ (T.map (QuotientGroup.mk' (gnC T))).index at h'
  rw [Subgroup.index_map, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _),
    Subgroup.index_top, mul_one] at h'
  exact h'.trans (Subgroup.index_dvd_of_le le_sup_left)

omit [Finite X] in
theorem comm_of_mem_gnImg {s : X} (hs : QuotientGroup.mk' (gnC T) s ∈ gnImg T T)
    {z : X} (hz : z ∈ omegaOneCenterOf T) : s * z * s⁻¹ = z := by
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 hs
  have hc : t⁻¹ * s ∈ gnC T := by
    rw [← QuotientGroup.eq]; exact hts
  obtain ⟨c, hc', rfl⟩ : ∃ c ∈ gnC T, s = t * c := ⟨t⁻¹ * s, hc, by group⟩
  have hzV : z ∈ gnV T := Subgroup.subset_normalClosure hz
  have h1 : t * z = z * t :=
    Subgroup.mem_centralizer_iff.1
      (A4.centerOf_le_centralizer T (A4.omegaOneCenterOf_le_centerOf T hz)) t ht
  have h2 : z * c = c * z := Subgroup.mem_centralizer_iff.1 hc' z hzV
  have hcz : c * z * c⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]; exact h2.symm
  calc t * c * z * (t * c)⁻¹ = t * (c * z * c⁻¹) * t⁻¹ := by group
    _ = t * z * t⁻¹ := by rw [hcz]
    _ = z := by rw [mul_inv_eq_iff_eq_mul]; exact h1

theorem not_isPSolvable_of_natural_on (hGN : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) {n : ℕ} (hn9 : 9 ≤ n)
    (g : ↥L →* alternatingGroup (Fin n)) (hg : Function.Surjective g)
    (W : Subgroup X) (hWV : W ≤ gnV T) (hZW : omegaOneCenterOf T ≤ W)
    (hWK : ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (π : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart n))
    (hπk : ∀ u, π u = 1 → ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
      (u u' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
          (g ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n)) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L) := by
  classical
  let mk : X →* X ⧸ gnC T := QuotientGroup.mk' (gnC T)
  let K : Subgroup X := L.comap mk
  let f : ↥K →* ↥L := (mk.comp K.subtype).codRestrict L (fun k => k.2)
  have hf : Function.Surjective f := by
    intro l
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (l : X ⧸ gnC T)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show mk x ∈ L
    rw [show mk x = (l : X ⧸ gnC T) from hx]
    exact l.2
  let Φ : ↥K →* alternatingGroup (Fin n) := g.comp f
  have hΦs : Function.Surjective Φ := hg.comp hf
  have hVab := I542.isElemAbelian_gnV T hGN
  have hVc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨v, hWV hv⟩ ⟨w, hWV hw⟩)
  have hV2 : ∀ v ∈ W, v * v = 1 := fun v hv => by
    have := hVab.2 v (hWV hv)
    simpa [pow_two] using this
  have hLsub : IsSubnormal L ⊤ := hL.2.1
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' hLsub (isSylowTwoOf_gnImg_top hGN)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S' : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ L
  let S : Subgroup X := S'.comap mk
  have hSK : S ≤ K := fun s hs => hs.2
  have hSsub : S.subgroupOf K = (S'.subgroupOf L).comap f := by
    ext k; exact Iff.rfl
  have hSodd : ¬ 2 ∣ (S.subgroupOf K).index := by
    rw [hSsub, Subgroup.index_comap_of_surjective _ hf]
    exact hSyl.2.2
  have himg : (S.subgroupOf K).map Φ = (S'.subgroupOf L).map g := by
    show Subgroup.map (g.comp f) _ = _
    rw [← Subgroup.map_map, hSsub, Subgroup.map_comap_eq_self_of_surjective hf]
  have hΦS : IsPGroup 2 ((S.subgroupOf K).map Φ) := by
    rw [himg]
    refine IsPGroup.map ?_ g
    exact hSyl.2.1.of_surjective (Subgroup.subgroupOfEquivOfLe hSyl.1).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSyl.1).symm.surjective
  have hΦodd : ¬ 2 ∣ ((S.subgroupOf K).map Φ).index := by
    rw [himg]
    intro hd
    exact hSyl.2.2 (hd.trans (Subgroup.index_map_dvd (S'.subgroupOf L) hg))
  have hSZ : ∀ s ∈ S, ∀ z ∈ omegaOneCenterOf T, s * z * s⁻¹ = z :=
    fun s hs z hz => comm_of_mem_gnImg hs.1 hz
  have hker : ∀ u : ↥⁅W, K⁆, π u = 1 → ∀ k ∈ K, (k : X) * u * (k : X)⁻¹ = u :=
    fun u hu => hπk u hu
  have hπ' : ∀ (l : ↥K) (u u' : ↥⁅W, K⁆), (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π u') = (QuotientAddGroup.mk
        (evenWeightPerm (Φ l : Equiv.Perm (Fin n)) x) : altHeart n) :=
    fun l u u' hu x hx => hπi (l : X) l.2 u u' hu x hx
  obtain ⟨φ, hφinj, D, hDc, hDΦ⟩ := exists_alt_eight_centralizing W K (omegaOneCenterOf T) S
    hWK hVc hV2 hZW hSK hSodd hSZ hn9 Φ hΦs hΦS hΦodd π hker hπ'
  intro hsolv
  let N : Subgroup ↥L := D.map f
  have hNle : N ≤ (gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L).subgroupOf L := by
    rintro _ ⟨d, hd, rfl⟩
    show ((f d : ↥L) : X ⧸ gnC T) ∈ gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L
    refine ⟨Subgroup.mem_map.2 ⟨(d : X), ?_, rfl⟩, (f d).2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (mul_inv_eq_iff_eq_mul.1 (hDc d hd z hz)).symm
  have hs1 : CFSG.HallHigman.IsPSolvable 3 ↥((gnImg T (Subgroup.centralizer
      (omegaOneCenterOf T : Set X)) ⊓ L).subgroupOf L) :=
    QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L ≤ L)).symm hsolv
  have hs2 : CFSG.HallHigman.IsPSolvable 3 ↥N := PSolvableClosure.isPSolvable_of_le hs1 hNle
  have hs3 : CFSG.HallHigman.IsPSolvable 3 ↥(N.map g) := PSolvableClosure.isPSolvable_map g hs2
  have hle : φ.range ≤ N.map g := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨d, hd, hda⟩ := hDΦ a
    exact ⟨f d, ⟨d, hd, rfl⟩, by rw [← hda]; rfl⟩
  have hs4 : CFSG.HallHigman.IsPSolvable 3 ↥φ.range := PSolvableClosure.isPSolvable_of_le hs3 hle
  have hs5 : CFSG.HallHigman.IsPSolvable 3 (alternatingGroup (Fin 8)) :=
    QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv (MonoidHom.ofInjective hφinj).symm hs4
  exact not_isPSolvable_three_alt_eight hs5

end Reduction

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

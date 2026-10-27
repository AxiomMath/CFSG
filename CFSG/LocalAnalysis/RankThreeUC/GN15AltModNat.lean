module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModGen
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModComm
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModRep
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.CGT.PushingUpLit.BHS
open CFSG.Quasithin.G6 hiding allOnes
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

abbrev gnPre (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  L.comap (QuotientGroup.mk' (gnC T))

omit [Finite X] in
theorem mem_normalizer_gnPre_iff {L : Subgroup (X ⧸ gnC T)} {x : X} :
    x ∈ Subgroup.normalizer (gnPre T L : Set X) ↔
      toStar T x ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := by
  have h1 := Subgroup.comap_normalizer_eq_of_surjective L (QuotientGroup.mk'_surjective (gnC T))
  constructor
  · intro hx
    have : x ∈ (Subgroup.normalizer (L : Set (X ⧸ gnC T))).comap (toStar T) := by
      rw [h1]; exact hx
    exact this
  · intro hx
    have : x ∈ (Subgroup.normalizer (L : Set (X ⧸ gnC T))).comap (toStar T) := hx
    rw [h1] at this
    exact this

section Layer

omit [Finite X] in
private theorem gn_phi_data {L : Subgroup (X ⧸ gnC T)} {n : ℕ}
    (g : ↥L →* alternatingGroup (Fin n)) (hg : Function.Surjective g)
    (hginj : Function.Injective g) {K : Subgroup X} (hK : K = gnPre T L) :
    ∃ Φ : ↥K →* alternatingGroup (Fin n), Function.Surjective Φ ∧
      (∀ (k : ↥K) (hk : toStar T k ∈ L), Φ k = g ⟨toStar T k, hk⟩) ∧
      ∀ k : ↥K, Φ k = 1 → (k : X) ∈ gnC T := by
  have hKmem : ∀ k : X, k ∈ K ↔ toStar T k ∈ L := fun k => by rw [hK]; rfl
  let f : ↥K →* ↥L := ((toStar T).comp K.subtype).codRestrict L (fun k => (hKmem k).1 k.2)
  have hf : Function.Surjective f := by
    intro l
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (l : X ⧸ gnC T)
    refine ⟨⟨x, (hKmem x).2 ?_⟩, Subtype.ext hx⟩
    show toStar T x ∈ L
    rw [show toStar T x = (l : X ⧸ gnC T) from hx]
    exact l.2
  refine ⟨g.comp f, hg.comp hf, fun k hk => rfl, fun k hk => ?_⟩
  have h1 : f k = 1 := hginj (by rw [show g (f k) = 1 from hk, map_one])
  have h2 : toStar T (k : X) = 1 := congrArg Subtype.val h1
  exact (QuotientGroup.eq_one_iff _).1 h2

omit [Finite X] in
private theorem gn_layer_ne_bot {L : Subgroup (X ⧸ gnC T)} {n : ℕ} (hn3 : 3 ≤ n)
    (e : ↥L ≃* alternatingGroup (Fin n)) {K M : Subgroup X} (hK : K = gnPre T L)
    (hVW : ⁅gnV T, K⁆ = M) : M ≠ ⊥ := by
  have hKmem : ∀ k : X, k ∈ K ↔ toStar T k ∈ L := fun k => by rw [hK]; rfl
  have hL1 : ∃ l : ↥L, l ≠ 1 := by
    have : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    obtain ⟨σ, hσ⟩ := exists_ne (1 : alternatingGroup (Fin n))
    exact ⟨e.symm σ, fun h => hσ (by simpa using congrArg e h)⟩
  intro h
  obtain ⟨l, hl⟩ := hL1
  apply hl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (l : X ⧸ gnC T)
  have hkK : k ∈ K := by
    rw [hKmem]
    show toStar T k ∈ L
    rw [show toStar T k = (l : X ⧸ gnC T) from hk]
    exact l.2
  have hkC : k ∈ gnC T := by
    show k ∈ Subgroup.centralizer (gnV T : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have : ⁅v, k⁆ ∈ (⁅gnV T, K⁆ : Subgroup X) := Subgroup.commutator_mem_commutator hv hkK
    rw [hVW, h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  apply Subtype.ext
  rw [← hk]
  exact (QuotientGroup.eq_one_iff k).2 hkC

private theorem gn_layer_perfle (hX : GNSetting X T) {n : ℕ} (hn5 : 5 ≤ n) {W K M : Subgroup X}
    (hM : M = ⁅W, K⁆) (hWV : W ≤ gnV T) (hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (Φ : ↥K →* alternatingGroup (Fin n)) (hΦ : Function.Surjective Φ)
    (hΦC : ∀ k : ↥K, Φ k = 1 → (k : X) ∈ gnC T) : M ≤ ⁅M, K⁆ := by
  have hVe : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  have hVc : ∀ v ∈ gnV T, ∀ w ∈ gnV T, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hCV : ∀ c ∈ gnC T, ∀ v ∈ gnV T, c * v * c⁻¹ = v := fun c hc v hv => by
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.1 hc v hv
    rw [← h1, mul_inv_cancel_right]
  subst hM
  exact altMod_commutator_perfect hn5 hWK (fun v hv w hw => hVc v (hWV hv) w (hWV hw)) Φ hΦ
    (fun k hk w hw => hCV _ (hΦC k hk) w (hWV hw))

theorem altMod_pi_surjective_of_layer (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)} {n : ℕ}
    (hn5 : 5 ≤ n) (e : ↥L ≃* alternatingGroup (Fin n))
    (g : ↥L →* alternatingGroup (Fin n)) (hg : Function.Surjective g)
    {W K M : Subgroup X} (hK : K = gnPre T L) (hM : M = ⁅W, K⁆) (hWV : W ≤ gnV T)
    (hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (π : ↥M →* Multiplicative (altHeart n))
    (hπk : ∀ u : ↥M, π u = 1 → ∀ k ∈ K, (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : X) (hl : toStar T l ∈ L) (u u' : ↥M),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
          (g ⟨toStar T l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n))
    (hVW : ⁅gnV T, K⁆ = M) : Function.Surjective π := by
  have hKmem : ∀ k : X, k ∈ K ↔ toStar T k ∈ L := fun k => by rw [hK]; rfl
  have hginj : Function.Injective g := (Finite.injective_iff_surjective_of_equiv e.toEquiv).2 hg
  obtain ⟨Φ, hΦ, hΦk, hΦC⟩ := gn_phi_data g hg hginj hK
  have hπi' : ∀ (l : ↥K) (u u' : ↥M), (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π u') =
        (QuotientAddGroup.mk (evenWeightPerm (Φ l : Equiv.Perm (Fin n)) x) : altHeart n) :=
    fun l u u' hu x hx => by
      have h := hπi (l : X) ((hKmem l).1 l.2) u u' hu x hx
      rwa [← hΦk l ((hKmem l).1 l.2)] at h
  exact altMod_pi_surjective (by omega) hM hWK Φ hΦ (gn_layer_ne_bot (by omega) e hK hVW)
    (gn_layer_perfle hX hn5 hM hWV hWK Φ hΦ hΦC) π hπk hπi'

theorem exists_altModRep_of_natural (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (hM2 : gnImg T (baum T) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    {n : ℕ} (hn9 : 9 ≤ n) (hodd : Odd n) (e : ↥L ≃* alternatingGroup (Fin n))
    (g : ↥L →* alternatingGroup (Fin n)) (hg : Function.Surjective g)
    {W K M : Subgroup X} (hK : K = gnPre T L) (hM : M = ⁅W, K⁆) (hWV : W ≤ gnV T)
    (hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (π : ↥M →* Multiplicative (altHeart n))
    (hπk : ∀ u : ↥M, π u = 1 → ∀ k ∈ K, (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : X) (hl : toStar T l ∈ L) (u u' : ↥M),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
          (g ⟨toStar T l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n))
    (hVW : ⁅gnV T, K⁆ = M) :
    ∃ ρ : ↥(Subgroup.normalizer (K : Set X)) →* Equiv.Perm (Fin n),
      (∀ (k : ↥K) (hk : toStar T k ∈ L), ρ ⟨k, Subgroup.le_normalizer k.2⟩ =
        (g ⟨toStar T k, hk⟩ : Equiv.Perm (Fin n))) ∧
      (∀ x : ↥(Subgroup.normalizer (K : Set X)), (x : X) ∈ gnC T → ρ x = 1) ∧
      (∃ T' : Set (Equiv.Perm (Fin n)), T'.Nonempty ∧ (∀ t ∈ T', t.IsSwap) ∧
        (∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) ∧
        ((thompsonJ T).subgroupOf (Subgroup.normalizer (K : Set X))).map ρ =
          Subgroup.closure T') ∧
      ((baum T).subgroupOf (Subgroup.normalizer (K : Set X))).map ρ ≤
        ((thompsonJ T).subgroupOf (Subgroup.normalizer (K : Set X))).map ρ := by
  classical
  have hn5 : 5 ≤ n := by omega
  have hn4 : 4 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hKmem : ∀ k : X, k ∈ K ↔ toStar T k ∈ L := fun k => by rw [hK]; rfl
  have hginj : Function.Injective g := (Finite.injective_iff_surjective_of_equiv e.toEquiv).2 hg
  have hVe : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  have hVT : gnV T ≤ T := gnV_le T hX
  have hVc : ∀ v ∈ gnV T, ∀ w ∈ gnV T, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hCV : ∀ c ∈ gnC T, ∀ v ∈ gnV T, c * v * c⁻¹ = v := fun c hc v hv => by
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.1 hc v hv
    rw [← h1, mul_inv_cancel_right]
  obtain ⟨Φ, hΦ, hΦk, hKC⟩ := gn_phi_data g hg hginj hK
  have hMW : M ≤ W := hM ▸ altMod_commutator_le_of_conj_mem hWK
  have hMV : M ≤ gnV T := hMW.trans hWV
  have hMT : M ≤ T := hMV.trans hVT
  have hMe : IsElemAbelian 2 M :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hVc _ (hMV a.2) _ (hMV b.2)),
      fun x hx => hVe.2 x (hMV hx)⟩
  have hMK : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M := fun k hk m hm => by
    subst hM
    exact altMod_conj_mem_commutator hWK hk hm
  have hNM : Subgroup.normalizer (K : Set X) ≤ Subgroup.normalizer (M : Set X) := by
    intro x hx
    have := altMod_mem_normalizer_commutator (mem_normalizer_gnV T x) hx
    rwa [hVW] at this
  have hL1 : ∃ l : ↥L, l ≠ 1 := by
    have : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    obtain ⟨σ, hσ⟩ := exists_ne (1 : alternatingGroup (Fin n))
    exact ⟨e.symm σ, fun h => hσ (by simpa using congrArg e h)⟩
  have hperfle : M ≤ ⁅M, K⁆ := gn_layer_perfle hX hn5 hM hWV hWK Φ hΦ hKC
  have hperf : ⁅K, M⁆ = M := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact altMod_commutator_le_of_conj_mem hMK
    · rw [Subgroup.commutator_comm]
      exact hperfle
  have hπi' : ∀ (l : ↥K) (u u' : ↥M), (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π u') =
        (QuotientAddGroup.mk (evenWeightPerm (Φ l : Equiv.Perm (Fin n)) x) : altHeart n) :=
    fun l u u' hu x hx => by
      have h := hπi (l : X) ((hKmem l).1 l.2) u u' hu x hx
      rwa [← hΦk l ((hKmem l).1 l.2)] at h
  have hπs : Function.Surjective π :=
    altMod_pi_surjective_of_layer hX hn5 e g hg hK hM hWV hWK π hπk hπi hVW
  let ψ' : ↥M →* ↥(coreMod n) := (altMod_toCore hodd).toMonoidHom.comp π
  have hψ : ∀ u, ψ' u = altMod_toCore hodd (π u) := fun u => rfl
  have hψs : Function.Surjective ψ' := (altMod_toCore hodd).surjective.comp hπs
  have hψe : ∀ (e' : ↥K) (w : ↥M) (hw : (e' : X) * w * (e' : X)⁻¹ ∈ M),
      ψ' ⟨(e' : X) * w * (e' : X)⁻¹, hw⟩ = coreAct n (Φ e' : Equiv.Perm (Fin n)) (ψ' w) := by
    intro e' w hw
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π w))
    have h1 := hπi' e' w ⟨_, hw⟩ rfl x hx.symm
    rw [hψ, hψ]
    have h2 : π ⟨(e' : X) * w * (e' : X)⁻¹, hw⟩ = Multiplicative.ofAdd
        (QuotientAddGroup.mk (evenWeightPerm (Φ e' : Equiv.Perm (Fin n)) x) : altHeart n) :=
      Multiplicative.toAdd.injective h1
    have h3 : π w = Multiplicative.ofAdd (QuotientAddGroup.mk x : altHeart n) :=
      Multiplicative.toAdd.injective hx.symm
    rw [h2, h3]
    exact altMod_toCore_equivar hodd _ x
  have hψk : ψ'.ker = (M ⊓ Subgroup.centralizer (K : Set X)).subgroupOf M := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have h0 : ψ' u = 1 ↔ π u = 1 := by rw [hψ]; exact MulEquiv.map_eq_one_iff _
    rw [h0]
    constructor
    · intro hu
      refine ⟨u.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact mul_inv_eq_iff_eq_mul.1 (hπk u hu h hh)
    · rintro ⟨-, hc⟩
      obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π u))
      have hfix : ∀ σ ∈ alternatingGroup (Fin n),
          (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) = QuotientAddGroup.mk x := by
        intro σ hσ
        obtain ⟨l, hl⟩ := hΦ ⟨σ, hσ⟩
        have hlu : (u : X) = (l : X) * u * (l : X)⁻¹ :=
          (mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hc (l : X) l.2)).symm
        have := hπi' l u u hlu x hx.symm
        rw [hl] at this
        rw [← this, ← hx]
      have h0 := altHeart_fixed_eq_zero hn4 x hfix
      apply Multiplicative.toAdd.injective
      rw [← hx, h0, toAdd_one]
  have hφk : Φ.ker = (K ⊓ Subgroup.centralizer (M : Set X)).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hk
      refine ⟨k.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (mul_inv_eq_iff_eq_mul.1 (hCV _ (hKC k hk) m (hMV hm))).symm
    · rintro ⟨-, hc⟩
      have hcore : coreAct n (Φ k : Equiv.Perm (Fin n)) = 1 := by
        refine MulEquiv.ext fun v => ?_
        obtain ⟨u, rfl⟩ := hψs v
        have hku : (k : X) * u * (k : X)⁻¹ = u :=
          mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hc u u.2).symm
        have hw : (k : X) * u * (k : X)⁻¹ ∈ M := by rw [hku]; exact u.2
        have h1 := hψe k u hw
        have h2 : (⟨(k : X) * u * (k : X)⁻¹, hw⟩ : ↥M) = u := Subtype.ext hku
        rw [h2] at h1
        rw [MulAut.one_apply]
        exact h1.symm
      have h1 : (Φ k : Equiv.Perm (Fin n)) = 1 := coreAct_injective hn3 (by rw [hcore, map_one])
      exact Subtype.ext h1
  have hNorm : ∀ x : X, toStar T x ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)) →
      x ∈ Subgroup.normalizer (K : Set X) := fun x hx => by
    have h1 := Subgroup.comap_normalizer_eq_of_surjective L (QuotientGroup.mk'_surjective (gnC T))
    have h2 : x ∈ (Subgroup.normalizer (L : Set (X ⧸ gnC T))).comap (toStar T) := hx
    rw [h1] at h2
    rw [hK]
    exact h2
  have hJK : thompsonJ T ≤ Subgroup.normalizer (K : Set X) := fun x hx =>
    hNorm x (thompsonJ_le_normalizer_of_isComponentOf hX hL (Subgroup.mem_map_of_mem _ hx))
  have hBK : baum T ≤ Subgroup.normalizer (K : Set X) := fun x hx =>
    hNorm x (hM2 (Subgroup.mem_map_of_mem _ hx))
  have hB : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (M : Set X) := by
    by_contra hcon
    push Not at hcon
    have hJc : thompsonJ T ≤ Subgroup.centralizer (M : Set X) :=
      iSup_le fun A => iSup_le fun hA => hcon A hA
    obtain ⟨l, hl⟩ := hL1
    have hbot : ⁅L, gnImg T (thompsonJ T)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro l' hl' j' hj'
      rw [Subgroup.mem_bot]
      obtain ⟨x, hxJ, rfl⟩ := Subgroup.mem_map.1 hj'
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective l'
      have hkK : k ∈ K := (hKmem k).2 hl'
      have hxN := hJK hxJ
      have hxm : ∀ m ∈ M, x * m * x⁻¹ = m := fun m hm =>
        mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 (hJc hxJ) m hm).symm
      have hxm' : ∀ m ∈ M, x⁻¹ * m * x = m := fun m hm => by
        have := hxm m hm
        calc x⁻¹ * m * x = x⁻¹ * (x * m * x⁻¹) * x := by rw [this]
          _ = m := by group
      have hzK : k * x * k⁻¹ * x⁻¹ ∈ K := by
        have h1 := (Subgroup.mem_normalizer_iff.1 hxN k⁻¹).1 (K.inv_mem hkK)
        have : k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) := by group
        rw [this]
        exact K.mul_mem hkK h1
      have hzc : k * x * k⁻¹ * x⁻¹ ∈ Subgroup.centralizer (M : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h1 := hxm' m hm
        have h2 : k⁻¹ * m * k ∈ M := by
          have := hMK k⁻¹ (K.inv_mem hkK) m hm
          simpa using this
        have h3 := hxm _ h2
        have h4 : (k * x * k⁻¹ * x⁻¹) * m * (k * x * k⁻¹ * x⁻¹)⁻¹ = m :=
          calc (k * x * k⁻¹ * x⁻¹) * m * (k * x * k⁻¹ * x⁻¹)⁻¹
              = k * (x * (k⁻¹ * (x⁻¹ * m * x) * k) * x⁻¹) * k⁻¹ := by group
            _ = k * (x * (k⁻¹ * m * k) * x⁻¹) * k⁻¹ := by rw [h1]
            _ = k * (k⁻¹ * m * k) * k⁻¹ := by rw [h3]
            _ = m := by group
        have h5 := mul_inv_eq_iff_eq_mul.1 h4
        exact h5.symm
      have hz1 : Φ ⟨k * x * k⁻¹ * x⁻¹, hzK⟩ = 1 := by
        have : (⟨k * x * k⁻¹ * x⁻¹, hzK⟩ : ↥K) ∈ Φ.ker := by
          rw [hφk, Subgroup.mem_subgroupOf]
          exact ⟨hzK, hzc⟩
        exact MonoidHom.mem_ker.1 this
      have hzC := hKC ⟨k * x * k⁻¹ * x⁻¹, hzK⟩ hz1
      show ⁅toStar T k, toStar T x⁆ = 1
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 hzC
    apply hl
    have hle : L ≤ ⊥ := hJ.symm.le.trans hbot.le
    exact Subtype.ext (Subgroup.mem_bot.1 (hle l.2))
  obtain ⟨ρ, hρe, hρJ, hρB⟩ := exists_altSwapRep hodd hn5 hX.sylow.2.1 hMe hMT hNM hperf
    Φ ψ' hΦ hφk hψs hψk hψe hJK hBK hB
  refine ⟨ρ, ?_, ?_, hρJ, hρB⟩
  · intro k hk
    have key : coreAct n (ρ ⟨k, Subgroup.le_normalizer k.2⟩) = coreAct n (Φ k : Equiv.Perm (Fin n)) := by
      refine MulEquiv.ext fun v => ?_
      obtain ⟨u, rfl⟩ := hψs v
      have hw := hMK k k.2 u u.2
      rw [← hρe ⟨k, Subgroup.le_normalizer k.2⟩ u hw, hψe k u hw]
    rw [coreAct_injective hn3 key]
    exact congrArg Subtype.val (hΦk k hk)
  · intro x hxC
    have key : coreAct n (ρ x) = 1 := by
      refine MulEquiv.ext fun v => ?_
      obtain ⟨u, rfl⟩ := hψs v
      have hw : (x : X) * u * (x : X)⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 (hNM x.2) u).1 u.2
      have h2 : (⟨(x : X) * u * (x : X)⁻¹, hw⟩ : ↥M) = u := Subtype.ext (hCV _ hxC u (hMV u.2))
      rw [← hρe x u hw, h2, MulAut.one_apply]
    exact coreAct_injective hn3 (by rw [key, map_one])

end Layer

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

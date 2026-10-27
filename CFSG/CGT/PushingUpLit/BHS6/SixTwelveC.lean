module

public import CFSG.CGT.PushingUpLit.BHS6.BlockThree
public import CFSG.CGT.PushingUpLit.BHS6.SixTwelve

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] noncomputable def autPre (V : Subgroup Γ) (U : Subgroup (MulAut ↥V)) : Subgroup Γ :=
  (U.comap (conjAct V)).map (Subgroup.normalizer (V : Set Γ)).subtype

theorem mem_autPre {V : Subgroup Γ} {U : Subgroup (MulAut ↥V)} {x : Γ} :
    x ∈ autPre V U ↔ ∃ hx : x ∈ Subgroup.normalizer (V : Set Γ), conjAct V ⟨x, hx⟩ ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem le_autPre_iff {V X : Subgroup Γ} {U : Subgroup (MulAut ↥V)}
    (hXV : X ≤ Subgroup.normalizer (V : Set Γ)) : X ≤ autPre V U ↔ autOn X V ≤ U := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := mem_autOn_iff.mp hy
    obtain ⟨hxN, hU⟩ := mem_autPre.mp (h hx)
    exact hU
  · intro h x hx
    exact mem_autPre.mpr ⟨hXV hx, h (mem_autOn_iff.mpr ⟨⟨x, hXV hx⟩, hx, rfl⟩)⟩

theorem mem_centralizer_sup_of_mem_autPre {V E G : Subgroup Γ} {x : Γ} (hxG : x ∈ G)
    (hEG : E ≤ G) (hx : x ∈ autPre V (autOn E V)) :
    x ∈ (G ⊓ Subgroup.centralizer (V : Set Γ)) ⊔ E := by
  obtain ⟨hxN, hxE⟩ := mem_autPre.mp hx
  obtain ⟨e, he, hee⟩ := mem_autOn_iff.mp hxE
  have hact : ∀ v : ↥V, (e : Γ) * v * (e : Γ)⁻¹ = x * v * x⁻¹ := fun v =>
    (conjAct_apply' V e v).trans ((congrArg (fun a : MulAut ↥V => ((a v : ↥V) : Γ)) hee).trans
      (conjAct_apply' V ⟨x, hxN⟩ v).symm)
  have hc : x * (e : Γ)⁻¹ ∈ Subgroup.centralizer (V : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hu : (e : Γ)⁻¹ * v * (e : Γ) ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set Γ)).inv_mem e.2) v).mp
        hv
      simpa using this
    have h : (e : Γ) * ((e : Γ)⁻¹ * v * (e : Γ)) * (e : Γ)⁻¹ =
        x * ((e : Γ)⁻¹ * v * (e : Γ)) * x⁻¹ := hact ⟨_, hu⟩
    have h1 : (e : Γ) * ((e : Γ)⁻¹ * v * (e : Γ)) * (e : Γ)⁻¹ = v := by group
    rw [h1] at h
    have h2 : v * x = x * ((e : Γ)⁻¹ * v * (e : Γ)) := by
      calc v * x = (x * ((e : Γ)⁻¹ * v * (e : Γ)) * x⁻¹) * x := by rw [← h]
        _ = x * ((e : Γ)⁻¹ * v * (e : Γ)) := by group
    calc v * (x * (e : Γ)⁻¹) = (v * x) * (e : Γ)⁻¹ := by group
      _ = (x * ((e : Γ)⁻¹ * v * (e : Γ))) * (e : Γ)⁻¹ := by rw [h2]
      _ = (x * (e : Γ)⁻¹) * v := by group
  have hxG' : x * (e : Γ)⁻¹ ∈ G ⊓ Subgroup.centralizer (V : Set Γ) :=
    ⟨G.mul_mem hxG (G.inv_mem (hEG he)), hc⟩
  have hx' : x = (x * (e : Γ)⁻¹) * (e : Γ) := by group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxG') (Subgroup.mem_sup_right he)

theorem conj_mem_autPre {V E : Subgroup Γ} {n x : Γ} (hnV : n ∈ Subgroup.normalizer (V : Set Γ))
    (hnE : n ∈ Subgroup.normalizer (E : Set Γ)) (hx : x ∈ autPre V (autOn E V)) :
    n * x * n⁻¹ ∈ autPre V (autOn E V) := by
  obtain ⟨hxN, hxE⟩ := mem_autPre.mp hx
  have hZV : Subgroup.zpowers n ≤ Subgroup.normalizer (V : Set Γ) :=
    Subgroup.zpowers_le.mpr hnV
  have hZE : Subgroup.zpowers n ≤ Subgroup.normalizer (E : Set Γ) :=
    Subgroup.zpowers_le.mpr hnE
  have hc : conjAct V ⟨n, hnV⟩ ∈ autOn (Subgroup.zpowers n) V :=
    mem_autOn_iff.mpr ⟨⟨n, hnV⟩, Subgroup.mem_zpowers n, rfl⟩
  have hcn := autOn_le_normalizer_autOn hZV hZE hc
  have hnxN : n * x * n⁻¹ ∈ Subgroup.normalizer (V : Set Γ) :=
    (Subgroup.normalizer (V : Set Γ)).mul_mem
      ((Subgroup.normalizer (V : Set Γ)).mul_mem hnV hxN)
      ((Subgroup.normalizer (V : Set Γ)).inv_mem hnV)
  refine mem_autPre.mpr ⟨hnxN, ?_⟩
  have e : conjAct V ⟨n * x * n⁻¹, hnxN⟩ =
      conjAct V ⟨n, hnV⟩ * conjAct V ⟨x, hxN⟩ * (conjAct V ⟨n, hnV⟩)⁻¹ := by
    show conjAct V (⟨n, hnV⟩ * ⟨x, hxN⟩ * ⟨n, hnV⟩⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hcn _).mp hxE

theorem btBlocksG_conjSub' {G T : Subgroup Γ} {g : Γ} (hg : g ∈ G) :
    btBlocksG G (A1b.conjSub g T) = btBlocksG G T := by
  ext E
  constructor
  · rintro ⟨h, hh, hE⟩
    exact ⟨h * g, G.mul_mem hh hg, by rwa [A1b.conjSub_mul]⟩
  · rintro ⟨h, hh, hE⟩
    refine ⟨h * g⁻¹, G.mul_mem hh (G.inv_mem hg), ?_⟩
    rwa [← A1b.conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem le_baumG_of_mem_btBlocksG {G T E : Subgroup Γ} (hE : E ∈ btBlocksG G T) :
    E ≤ baumG G T := by
  obtain ⟨g, hg, hEb⟩ := hE
  rw [← hEb.commutator]
  refine Subgroup.commutator_le.mpr fun e he b hb => ?_
  have hbe : e * b * e⁻¹ ∈ baumG G T := by
    have h1 : e * b * e⁻¹ ∈ baum (A1b.conjSub (e * g) T) := by
      have : baum (A1b.conjSub (e * g) T) = A1b.conjSub e (baum (A1b.conjSub g T)) := by
        rw [A1b.conjSub_mul, baum_conjSub]
      rw [this, A1b.mem_conjSub_iff]
      have h3 : e⁻¹ * (e * b * e⁻¹) * e = b := by group
      rw [h3]
      exact hb
    exact baum_conjSub_le_baumG (G.mul_mem (hEb.le he) hg) h1
  have hb' : b ∈ baumG G T := baum_conjSub_le_baumG hg hb
  have : ⁅e, b⁆ = (e * b * e⁻¹) * b⁻¹ := rfl
  rw [this]
  exact (baumG G T).mul_mem hbe ((baumG G T).inv_mem hb')

section Finite

variable [Finite Γ] {G T E F : Subgroup Γ}

omit [Finite Γ] in
theorem baumG_le (hT : IsSylowTwoOf T G) : baumG G T ≤ G :=
  iSup₂_le fun y hy => (inf_le_left : baum (A1b.conjSub y T) ≤ _).trans
    (isSylowTwoOf_conjSub_of_mem hT hy).1

theorem baumG_le_autPre_of_linear (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hsub : CFSG.Open.IsSubnormal E G) {n : ℕ} (hn2 : 2 ≤ n) (hn : IsNaturalSLTwoModule ↥E n) :
    baumG G T ≤ autPre (pCoreOf 2 E) (autOn E (pCoreOf 2 E)) := by
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  obtain ⟨-, hBN⟩ := six_twelve_a hG hT (mem_btBlocksG_of_isBTBlock hE) hsub
  have hEW : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := le_normalizer_pCoreOf_self E
  have hNW : Subgroup.normalizer (E : Set Γ) ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E
  have hbase : baum T ≤ autPre (pCoreOf 2 E) (autOn E (pCoreOf 2 E)) := by
    have h1 := (block_structure_sl hG hT hE hn2 hn).1
    rw [blockW_eq_pCoreOf hE] at h1
    exact (le_autPre_iff (baum_le_normalizer_of_isBTBlock hE |>.trans hNW)).mpr h1
  refine iSup₂_le fun x hx => ?_
  have hTx : IsSylowTwoOf (A1b.conjSub x T) G := isSylowTwoOf_conjSub_of_mem hT' hx
  have hB1 : baum T ≤ baumG G T := by
    have := baum_conjSub_le_baumG (G := G) (T := T) (x := 1) G.one_mem
    rwa [A1b.conjSub_one] at this
  obtain ⟨c, hc, hcb⟩ := exists_conj_baum_of_le_of_le (N := baumG G T) hT' hTx (baumG_le hT') hB1
    (baum_conjSub_le_baumG hx)
  intro b hb
  rw [hcb, A1b.mem_conjSub_iff] at hb
  have hb0 : c⁻¹ * b * c ∈ baum T := hb
  have hcE : c ∈ Subgroup.normalizer (E : Set Γ) := hBN hc
  have h2 := conj_mem_autPre (hnV := hNW hcE) hcE (hbase hb0)
  have : c * (c⁻¹ * b * c) * c⁻¹ = b := by group
  rwa [this] at h2

theorem sq_mem_autOn_of_mem_normalizer_symm (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) {m : ℕ} (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m) {W : Subgroup Γ}
    (hWE : W = pCoreOf 2 E) (hWe : IsElemAbelian 2 W) {y : MulAut ↥W}
    (hy : y ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) : y ^ 2 ∈ autOn E W := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  obtain ⟨D, ψ, hψ, -, hψb, -⟩ := block_structure_symm hG hT hE hm hn hWE hWe
  have h3 : 3 ≤ 2 * m + 1 := by omega
  let y' : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) := ⟨y, hy⟩
  have hπ : ψ (y' ^ 2) ∈ alternatingGroup (Fin (2 * m + 1)) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_pow, map_pow, Int.units_sq]
  obtain ⟨e, he⟩ := D.θ.surjective ⟨ψ (y' ^ 2), hπ⟩
  have hψe : ψ ⟨(e : MulAut ↥W), Subgroup.le_normalizer e.2⟩ = ψ (y' ^ 2) := by
    have := D.perm_unique h3 (π := ψ ⟨(e : MulAut ↥W), Subgroup.le_normalizer e.2⟩)
      (π' := ((D.θ e : alternatingGroup (Fin (2 * m + 1))) : Equiv.Perm (Fin (2 * m + 1))))
      (fun w => (hψ ⟨(e : MulAut ↥W), Subgroup.le_normalizer e.2⟩ w).symm.trans
        (D.equivar e w))
    rw [this, he]
  have hinj := hψb.1 hψe
  have h2 : y ^ 2 = (e : MulAut ↥W) := congrArg Subtype.val hinj.symm
  rw [h2]
  exact e.2

theorem le_autPre_of_opResidual_symm (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) {m : ℕ} (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m) {W : Subgroup Γ}
    (hWE : W = pCoreOf 2 E) (hWe : IsElemAbelian 2 W) (hF : opResidual 2 F = F)
    (hFN : F ≤ Subgroup.normalizer (E : Set Γ)) : F ≤ autPre W (autOn E W) := by
  have hNW : Subgroup.normalizer (E : Set Γ) ≤ Subgroup.normalizer (W : Set Γ) := by
    rw [hWE]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E
  have hFW : F ≤ Subgroup.normalizer (W : Set Γ) := hFN.trans hNW
  rw [← hF]
  refine opResidual_le_of_pow_mem fun x hx => ⟨1, ?_⟩
  rw [pow_one]
  have hxN : x ∈ Subgroup.normalizer (W : Set Γ) := hFW hx
  have hx2N : x ^ 2 ∈ Subgroup.normalizer (W : Set Γ) := Subgroup.pow_mem _ hxN 2
  refine mem_autPre.mpr ⟨hx2N, ?_⟩
  have hcx : conjAct W ⟨x, hxN⟩ ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hFW hFN (mem_autOn_iff.mpr ⟨⟨x, hxN⟩, hx, rfl⟩)
  have e1 : (⟨x ^ 2, hx2N⟩ : ↥(Subgroup.normalizer (W : Set Γ))) = ⟨x, hxN⟩ ^ 2 :=
    Subtype.ext (by simp)
  rw [e1, map_pow]
  exact sq_mem_autOn_of_mem_normalizer_symm hG hT hE hm hn hWE hWe hcx

theorem le_autPre_of_le_baumG (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hsub : CFSG.Open.IsSubnormal E G) (hF : opResidual 2 F = F) (hFB : F ≤ baumG G T) :
    F ≤ autPre (pCoreOf 2 E) (autOn E (pCoreOf 2 E)) := by
  obtain ⟨-, hBN⟩ := six_twelve_a hG hT (mem_btBlocksG_of_isBTBlock hE) hsub
  rcases hE.type with ⟨n, hn2, hn⟩ | ⟨m, hm, hn⟩
  · exact hFB.trans (baumG_le_autPre_of_linear hG hT hE hsub hn2 hn)
  · exact le_autPre_of_opResidual_symm hG hT hE hm hn rfl
      (isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2) hF (hFB.trans hBN)

theorem six_twelve_c (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : E ∈ btBlocksG G T)
    (hsub : CFSG.Open.IsSubnormal E G) (hF : F ∈ btBlocksG G T) : F ≤ E ∨ ⁅F, E⁆ = ⊥ := by
  obtain ⟨g, hg, hE₀⟩ := hE
  have hT₀' : IsSylowTwoOf (A1b.conjSub g T) G :=
    isSylowTwoOf_conjSub_of_mem (isSylowTwoOf_of_isSylowOf hT) hg
  have hT₀ : IsSylowOf 2 (A1b.conjSub g T) G := isSylowOf_of_isSylowTwoOf hT₀'
  have hF₀ : F ∈ btBlocksG G (A1b.conjSub g T) := by rwa [btBlocksG_conjSub' hg]
  have hFB : F ≤ baumG G (A1b.conjSub g T) := le_baumG_of_mem_btBlocksG hF₀
  obtain ⟨-, hBN⟩ := six_twelve_a hG hT₀ (mem_btBlocksG_of_isBTBlock hE₀) hsub
  have hFN : F ≤ Subgroup.normalizer (E : Set Γ) := hFB.trans hBN
  obtain ⟨h, hh, hFh⟩ := hF₀
  have hFres : opResidual 2 F = F := opResidual_eq_of_isBTBlock hFh
  have hFpre := le_autPre_of_le_baumG hG hT₀ hE₀ hsub hFres hFB
  have hFG : F ≤ G := hFh.le
  have hFR : F ≤ (G ⊓ Subgroup.centralizer (blockW E : Set Γ)) ⊔ E := by
    rw [blockW_eq_pCoreOf hE₀]
    intro x hx
    exact mem_centralizer_sup_of_mem_autPre (hFG hx) hE₀.le (hFpre hx)
  rcases six_seven_of_le_R hG hT₀ hE₀ ⟨h, hh, hFh⟩ hFN hFR with h1 | ⟨h1, -⟩
  · right
    rw [Subgroup.commutator_comm]
    exact h1
  · exact Or.inl h1

end Finite

end CFSG.CGT.PushingUpLit.BHS6

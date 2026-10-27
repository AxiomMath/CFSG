module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldY
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import TauCeti.GroupTheory.PGroup
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

open CFSG.Open CFSG.Goldschmidt Subgroup CFSG.GH74.GLS.Th2.P412
open CFSG.LocalCores
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

namespace CFSG.OddStandard.SmallF3.Omega

private theorem s888_isComponent_iff_openComponentOf {Y : Type} [Group Y] (K : Subgroup Y) :
    IsComponent K ↔ CFSG.Open.IsComponentOf K ⊤ := by
  unfold IsComponent CFSG.Open.IsComponentOf
  rw [CFSG.Open.IsSubnormal.top_iff, ← (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1]
  exact ⟨fun h => ⟨le_top, h.2, h.1⟩, fun h => ⟨h.2.2, h.2.1⟩⟩

private theorem s888_goldschmidtLayer_eq_layer {Y : Type} [Group Y] :
    goldschmidtLayer Y = layer Y := by
  rw [goldschmidtLayer.eq_sSup, CFSG.layer.eq_sSup]
  congr 1
  ext K
  exact (s888_isComponent_iff_openComponentOf K).symm

private theorem s888_component_center_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hZY : center Y = ⊥) (hlayer : goldschmidtLayer Y = ⊤)
    {K : Subgroup Y} (hK : IsComponent K) : center ↥K = ⊥ :=
  GoldY.component_center_eq_bot hZY hlayer ((s888_isComponent_iff_openComponentOf K).1 hK)

private theorem s888_goldschmidtSimpleType_of_mulEquiv {L M : Type} [Group L] [Group M]
    (h : goldschmidtSimpleType L) (e : L ≃* M) : goldschmidtSimpleType M := by
  classical
  simp only [goldschmidtSimpleType] at h ⊢
  rcases h with ⟨f, hf, hne⟩ | ⟨n, hn, hne⟩ | ⟨f, hf, hne⟩ |
    ⟨p, f, hp, hpo, hf, hp5, h8, hne⟩ | ⟨m, hm, hcard⟩ | hne
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans hne.some⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans hne.some⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans hne.some⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, f, hp, hpo, hf, hp5, h8, ⟨e.symm.trans hne.some⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, (Nat.card_congr e.toEquiv).symm.trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans hne.some⟩))))

private theorem s888_pi_eval_surjective {ι : Type*} (i : ι) {G : ι → Type*}
    [∀ i, Group (G i)] : Function.Surjective (Pi.evalMonoidHom G i) := by
  classical
  exact fun y => ⟨Pi.mulSingle i y, Pi.mulSingle_eq_same i y⟩

private noncomputable def s888_piEquiv {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]
    (S : ∀ i, Subgroup (G i)) :
    (∀ i, S i) ≃* (Subgroup.pi Set.univ fun i => (S i : Subgroup (G i))) where
  toFun x := ⟨fun i => (x i : G i), (Subgroup.mem_pi Set.univ).mpr fun i _ => (x i).2⟩
  invFun x := fun i => ⟨x.1 i, (Subgroup.mem_pi Set.univ).mp x.2 i (Set.mem_univ i)⟩
  left_inv x := by funext i; rfl
  right_inv x := by ext i; rfl
  map_mul' x y := by ext i; rfl

private theorem s888_isPGroup_pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    {p : ℕ} {S : ∀ i, Subgroup (G i)} (h : ∀ i, IsPGroup p (S i)) :
    IsPGroup p (Subgroup.pi Set.univ S) :=
  (IsPGroup.pi h).of_equiv (s888_piEquiv G S)

private theorem s888_sylow_eq_pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [Finite (∀ i, G i)] {p : ℕ} [Fact p.Prime] (S : Sylow p (∀ i, G i)) :
    (S : Subgroup (∀ i, G i)) =
      Subgroup.pi Set.univ (fun i =>
        (S.mapSurjective (s888_pi_eval_surjective i) : Subgroup (G i))) :=
  (S.is_maximal'
    (s888_isPGroup_pi (fun i => (S.mapSurjective (s888_pi_eval_surjective i)).isPGroup'))
    (fun x hx i _ => ⟨x, hx, rfl⟩)).symm

private theorem s888_omega1_central_of_goldtype (hN11a : S_N11a) (hN11c : S_N11c)
    {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (htype : goldschmidtSimpleType K) (S : Sylow 2 K)
    (hcomm : IsMulCommutative (Omega1 (S : Subgroup K))) :
    ∀ z ∈ Omega1 (S : Subgroup K), ∀ w ∈ (S : Subgroup K), z * w = w * z := by
  obtain ⟨hab, hnab⟩ := hN11a K htype S hcomm
  by_cases hSab : IsMulCommutative (S : Subgroup K)
  · intro z hz w hw
    exact congrArg Subtype.val (hSab.is_comm.comm ⟨z, GoldType.omega1_le _ hz⟩ ⟨w, hw⟩)
  · intro z hz w hw
    obtain ⟨hΩZ, -⟩ := hN11c K (hnab hSab) S
    exact ((mem_sylowCenter.mp (hΩZ ▸ hz)).2 w hw).symm

private theorem s888_omega1_le_pi {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)]
    (T : Subgroup (∀ i, G i)) (S : ∀ i, Subgroup (G i))
    (hT : T = Subgroup.pi Set.univ S) :
    Omega1 T ≤ Subgroup.pi Set.univ (fun i => Omega1 (S i)) := by
  show Subgroup.closure {x | x ∈ T ∧ x ^ 2 = 1} ≤ Subgroup.pi Set.univ _
  rw [Subgroup.closure_le]
  rintro x ⟨hxT, hx2⟩
  refine (Subgroup.mem_pi Set.univ).mpr fun i _ => ?_
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [hT] at hxT
    exact (Subgroup.mem_pi Set.univ).mp hxT i (Set.mem_univ i)
  · have := congrFun hx2 i
    simpa using this

private theorem s888_omega1_map_mulSingle_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, Group (G i)] (T : Subgroup (∀ i, G i)) (S : ∀ i, Subgroup (G i))
    (hT : T = Subgroup.pi Set.univ S) (i : ι) :
    (Omega1 (S i)).map (MonoidHom.mulSingle G i) ≤ Omega1 T := by
  classical
  show (Subgroup.closure {z | z ∈ S i ∧ z ^ 2 = 1}).map (MonoidHom.mulSingle G i) ≤
    Subgroup.closure {x | x ∈ T ∧ x ^ 2 = 1}
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨z, ⟨hzS, hz2⟩, rfl⟩
  change (MonoidHom.mulSingle G i) z ∈ T ∧ ((MonoidHom.mulSingle G i) z) ^ 2 = 1
  refine ⟨?_, ?_⟩
  · rw [hT]
    refine (Subgroup.mem_pi Set.univ).mpr fun j _ => ?_
    by_cases hji : j = i
    · subst hji; simpa using hzS
    · change Pi.mulSingle i z j ∈ S j
      rw [Pi.mulSingle_eq_of_ne hji]
      exact (S j).one_mem
  · rw [← map_pow, hz2, map_one]

theorem omega1_commutes_of_layer (hN11a : S_N11a) (hN11c : S_N11c) {Y : Type} [Group Y] [Finite Y]
    (hO2 : CFSG.Open.pCore 2 Y = ⊥) (hO2' : goldschmidtOddCore Y = ⊥)
    (hlayer : goldschmidtLayer Y = ⊤)
    (hc : ∀ K : Subgroup Y, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K))
    (T : Sylow 2 Y) (hΩ : IsMulCommutative (Omega1 (T : Subgroup Y))) :
    ∀ t ∈ (T : Subgroup Y), ∀ d ∈ Omega1 (T : Subgroup Y), t * d = d * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZY : center Y = ⊥ := GoldY.center_eq_bot hO2 hO2' hlayer
  have hlayer' : layer Y = ⊤ := by rw [← s888_goldschmidtLayer_eq_layer]; exact hlayer
  have hcenter : ∀ K : ComponentIndex Y, center ↥(K.1) = ⊥ := fun K =>
    s888_component_center_eq_bot hZY hlayer K.2
  have hinj : Function.Injective (layerMul Y) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    funext K
    have hK : x K ∈ center ↥(K.1) :=
      (Subgroup.mem_pi Set.univ).mp (layerMul_ker_le hx) K (Set.mem_univ K)
    rw [hcenter K, Subgroup.mem_bot] at hK
    exact hK
  have hsurj : Function.Surjective (layerMul Y) := by
    rw [← MonoidHom.range_eq_top, layerMul_range, hlayer']
  let e : (∀ K : ComponentIndex Y, ↥(K.1)) ≃* Y :=
    MulEquiv.ofBijective (layerMul Y) ⟨hinj, hsurj⟩
  let T' : Sylow 2 (∀ K : ComponentIndex Y, ↥(K.1)) :=
    T.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hT'coe : (T' : Subgroup (∀ K : ComponentIndex Y, ↥(K.1))) =
      (T : Subgroup Y).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T
  let SK : ∀ K : ComponentIndex Y, Sylow 2 ↥(K.1) := fun K =>
    T'.mapSurjective (s888_pi_eval_surjective K)
  have hT'pi : (T' : Subgroup (∀ K : ComponentIndex Y, ↥(K.1))) =
      Subgroup.pi (Set.univ : Set (ComponentIndex Y))
        (fun K => (SK K : Subgroup ↥(K.1))) :=
    s888_sylow_eq_pi T'
  have homega_le : Omega1 (T' : Subgroup (∀ K : ComponentIndex Y, ↥(K.1))) ≤
      Subgroup.pi (Set.univ : Set (ComponentIndex Y))
        (fun K => Omega1 (SK K : Subgroup ↥(K.1))) :=
    s888_omega1_le_pi _ _ hT'pi
  have hΩ' : IsMulCommutative (Omega1 (T' : Subgroup (∀ K : ComponentIndex Y, ↥(K.1)))) := by
    rw [hT'coe, GoldY.omega1_map e.symm.toMonoidHom e.symm.injective]
    exact isMulCommutative_map hΩ e.symm.toMonoidHom
  have hcentral : ∀ K : ComponentIndex Y,
      ∀ z ∈ Omega1 (SK K : Subgroup ↥(K.1)), ∀ w ∈ (SK K : Subgroup ↥(K.1)), z * w = w * z := by
    intro K
    let eK : ↥(K.1) ⧸ center ↥(K.1) ≃* ↥(K.1) :=
      (QuotientGroup.quotientMulEquivOfEq (hcenter K)).trans QuotientGroup.quotientBot
    haveI : IsSimpleGroup (↥(K.1) ⧸ center ↥(K.1)) := K.2.1.2.1
    haveI : IsSimpleGroup ↥(K.1) := eK.symm.isSimpleGroup
    have htype : goldschmidtSimpleType ↥(K.1) :=
      s888_goldschmidtSimpleType_of_mulEquiv
        (hc K.1 ((s888_isComponent_iff_openComponentOf K.1).1 K.2)) eK
    refine s888_omega1_central_of_goldtype hN11a hN11c htype (SK K) ?_
    refine GoldY.isMulCommutative_of_map
      (MonoidHom.mulSingle (fun K : ComponentIndex Y => ↥(K.1)) K)
      (fun a b h => Pi.mulSingle_injective K h) ?_
    exact GoldY.isMulCommutative_of_le
      (s888_omega1_map_mulSingle_le _ _ hT'pi K) hΩ'
  intro t ht d hd
  let x : (∀ K : ComponentIndex Y, ↥(K.1)) := e.symm t
  let y : (∀ K : ComponentIndex Y, ↥(K.1)) := e.symm d
  have hxT' : x ∈ (T' : Subgroup (∀ K : ComponentIndex Y, ↥(K.1))) := by
    rw [hT'coe]
    exact Subgroup.mem_map_of_mem _ ht
  have hyΩ : y ∈ Omega1 (T' : Subgroup (∀ K : ComponentIndex Y, ↥(K.1))) := by
    rw [hT'coe, GoldY.omega1_map e.symm.toMonoidHom e.symm.injective]
    exact Subgroup.mem_map_of_mem _ hd
  have hyx : y * x = x * y := by
    funext K
    have hyK : y K ∈ Omega1 (SK K : Subgroup ↥(K.1)) :=
      (Subgroup.mem_pi Set.univ).mp (homega_le hyΩ) K (Set.mem_univ K)
    have hxK : x K ∈ (SK K : Subgroup ↥(K.1)) := ⟨x, hxT', rfl⟩
    simpa using hcentral K (y K) hyK (x K) hxK
  have h : d * t = t * d := by
    have := congrArg e hyx
    simpa [x, y] using this
  exact h.symm

end CFSG.OddStandard.SmallF3.Omega

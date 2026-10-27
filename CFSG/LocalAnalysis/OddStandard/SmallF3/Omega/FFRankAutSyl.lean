module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutAlg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutBfs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutMat

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffRA_projSim_elemAb_le [Finite (ProjSim Q)] (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2) (hd : ∀ i, d i ≠ 0)
    {n k m bound : ℕ} (hn : n = 2 ^ k) (hm : Odd m) (hcard : Nat.card (ProjSim Q) = n * m)
    (hs : FFRASide n d true bound) (E : Subgroup (ProjSim Q)) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ bound := by
  obtain ⟨e, one, mul, 𝓛, he, hone, hmul, h0, h1, h2⟩ := ffRA_exists_table b hb hd hs
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hE x.1 x.2)⟩
  obtain ⟨g, hg⟩ := ffRA_exists_conj_range e he one hone mul hmul hn hm hcard hE2
  have hK : ∀ y ∈ E.map (MulAut.conj g).toMonoidHom, ∃ i, e i = y := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hKe : ∀ y ∈ E.map (MulAut.conj g).toMonoidHom, y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE x hx, map_one]
  have h2' : ∀ H ∈ 𝓛, ∀ x : Fin n, x ∉ H → mul x x = one → (∀ h ∈ H, mul x h = mul h x) →
      H ∪ H.image (mul x) ∈ 𝓛 := fun H hH x hx hxx hc => h2 H hH x hx (by simpa using hxx) hc
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]
  exact ffRA_bfs_elemAb e he one hone mul hmul 𝓛 h0 h1 h2' hK hKe

theorem ffRA_projSim_abelian_le [Finite (ProjSim Q)] (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2) (hd : ∀ i, d i ≠ 0)
    {n k m bound : ℕ} (hn : n = 2 ^ k) (hm : Odd m) (hcard : Nat.card (ProjSim Q) = n * m)
    (hs : FFRASide n d false bound) (E : Subgroup (ProjSim Q)) (hp : IsPGroup 2 E)
    (hc : IsMulCommutative E) : Nat.card E ≤ bound := by
  obtain ⟨e, one, mul, 𝓛, he, hone, hmul, h0, h1, h2⟩ := ffRA_exists_table b hb hd hs
  obtain ⟨g, hg⟩ := ffRA_exists_conj_range e he one hone mul hmul hn hm hcard hp
  have hK : ∀ y ∈ E.map (MulAut.conj g).toMonoidHom, ∃ i, e i = y := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hKp : IsPGroup 2 (E.map (MulAut.conj g).toMonoidHom) :=
    hp.of_equiv (Subgroup.equivMapOfInjective E _ (MulAut.conj g).injective)
  haveI := hc
  have hKc : IsMulCommutative (E.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.map_isMulCommutative E _
  have h2' : ∀ H ∈ 𝓛, ∀ x : Fin n, x ∉ H → mul x x ∈ H → (∀ h ∈ H, mul x h = mul h x) →
      H ∪ H.image (mul x) ∈ 𝓛 := fun H hH x hx hxx hc => h2 H hH x hx (by simpa using hxx) hc
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]
  exact ffRA_bfs_abelian e he one hone mul hmul 𝓛 h0 h1 h2' hK hKp hKc

end CFSG.OddStandard.SmallF3.Omega

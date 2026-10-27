module

public import CFSG.Fischer.Classification.Step0
public import CFSG.Fischer.Classification.Step1
public import CFSG.Fischer.Classification.PSU6
public import CFSG.Fischer.Classification.Basic.Trichotomy
public import CFSG.Fischer.NoF25

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer

theorem noF25Input :
    NoF25Input :=
  fun _ _ _ hP _ he hT hZ hS => CFSG.Fischer.not_F25 hP he hT hZ hS

theorem statement_of_remaining
    (h3 : O3InputI) (h2 : O2InputI) (hC : ClassicalPartIIIInputI) :
    Statement :=
  statement_of_inputsI s3Input symplecticInput trichotomyInput h3 h2
    (partIIIInputI_of_classical hC noF25Input psu6Input)

end CFSG.Fischer.Classification
